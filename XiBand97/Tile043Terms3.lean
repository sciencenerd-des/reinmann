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
namespace Reinmann.XiBand97.Tile043Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35769/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35769/1280))
  have he : value ((69/80), (35769/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-22364231/8388608), (-1449177875/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-20121310647785/18014398509481984), (626172760899241/9007199254740992)), (204323185/9007199254740992), by norm_num⟩
  | 1 => ⟨((29657281/8589934592), (-1845861995/8589934592)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((-22917979/4294967296), (1426409447/4294967296)), (469/4294967296), by norm_num⟩
  | 3 => ⟨((11806741/2147483648), (-734848693/2147483648)), (485/4294967296), by norm_num⟩
  | 4 => ⟨((-18247569/4294967296), (1135724253/4294967296)), (377/4294967296), by norm_num⟩
  | 5 => ⟨((5640401/2147483648), (-1404228753/8589934592)), (117/2147483648), by norm_num⟩
  | 6 => ⟨((-5811573/4294967296), (1446843563/17179869184)), (121/4294967296), by norm_num⟩
  | 7 => ⟨((20530079/34359738368), (-319446777/8589934592)), (429/34359738368), by norm_num⟩
  | 8 => ⟨((-31729673/137438953472), (1974847099/137438953472)), (665/137438953472), by norm_num⟩
  | 9 => ⟨((21795059/274877906944), (-169564895/34359738368)), (459/274877906944), by norm_num⟩
  | 10 => ⟨((-26947781/1099511627776), (1677223325/1099511627776)), (569/1099511627776), by norm_num⟩
  | 11 => ⟨((15144861/2199023255552), (-942612455/2199023255552)), (321/2199023255552), by norm_num⟩
  | 12 => ⟨((-31208939/17592186044416), (242804593/2199023255552)), (83/2199023255552), by norm_num⟩
  | 13 => ⟨((29682509/70368744177664), (-1847432135/70368744177664)), (317/35184372088832), by norm_num⟩
  | 14 => ⟨((-1638391/17592186044416), (1631568903/281474976710656)), (281/140737488355328), by norm_num⟩
  | 15 => ⟨((10803917/562949953421312), (-336216583/281474976710656)), (465/1125899906842624), by norm_num⟩
  | 16 => ⟨((-16697683/4503599627370496), (2078519463/9007199254740992)), (721/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (516766181719/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777854633359907/633825300114114700748351602688), (2443875995285/633825300114114700748351602688)), (184881/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472178383194431/9903520314283042199192993792), (1374362427235/19807040628566084398385987584)), (208023/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944212217438991/1237940039285380274899124224), (2919725853727/2475880078570760549798248448)), (55265/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885045397714109/77371252455336267181195264), (2918832639655/154742504910672534362390528)), (221101/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193565299337771/1208925819614629174706176), (683864225327/2417851639229258349412352)), (51831/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257886649889687/604462909807314587353088), (598144118641/151115727451828646838272)), (45363/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235790807718811/9444732965739290427392), (3886159498549/75557863725914323419136)), (73735/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296440459555521/4722366482869645213696), (2913065326291/4722366482869645213696)), (55319/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202492164087845/73786976294838206464), (4002940619083/590295810358705651712)), (19023/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821586587398451/73786976294838206464), (2499946070657/36893488147419103232)), (47579/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820533493944991/9223372036854775808), (2809840253537/4611686018427387904)), (13389/288230376151711744), by norm_num⟩
  | 6 => ⟨((1591782789763397/1152921504606846976), (5613189326345/1152921504606846976)), (53593/144115188075855872), by norm_num⟩
  | 5 => ⟨((298163491457979/36028797018963968), (4904247024023/144115188075855872)), (375485/144115188075855872), by norm_num⟩
  | 4 => ⟨((744374495385197/18014398509481984), (7341805592597/36028797018963968)), (70487/4503599627370496), by norm_num⟩
  | 3 => ⟨((185706287646219/1125899906842624), (9151818513079/9007199254740992)), (706041/9007199254740992), by norm_num⟩
  | 2 => ⟨((555185691385865/1125899906842624), (2278440243169/562949953421312)), (1415603/4503599627370496), by norm_num⟩
  | 1 => ⟨((34458117417543/35184372088832), (27151694915109/2251799813685248)), (2132239/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159260424020171/2251799813685248), (53549223762087/2251799813685248)), (4299993/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159260424020171/2251799813685248), (53549223762087/2251799813685248)), (16403171547896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2069250575053803/2251799813685248), (25674289273797/562949953421312)), (4225539/1125899906842624), by norm_num⟩
  | 2 => ⟨((237102073324117/281474976710656), (1474557638323/17592186044416)), (8151391/1125899906842624), by norm_num⟩
  | 3 => ⟨((1581974151919165/2251799813685248), (317978149980533/2251799813685248)), (30198449/2251799813685248), by norm_num⟩
  | 4 => ⟨((1066494498702805/2251799813685248), (111695811298835/562949953421312)), (25479891/1125899906842624), by norm_num⟩
  | 5 => ⟨((26029046906075/140737488355328), (423209798861827/2251799813685248)), (136986077/4503599627370496), by norm_num⟩
  | 6 => ⟨((-20121310647785/18014398509481984), (626172760899241/9007199254740992)), (204323185/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1449177875/16777216)), (1/8388608), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-735009129/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((567249539589225/9007199254740992), (407295658016457/18014398509481984)), (204114433/18014398509481984), by norm_num⟩
  | 1 => ⟨((-848106217/4294967296), (-304477973/4294967296)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((1329616069/4294967296), (238672231/2147483648)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((-1389667831/4294967296), (-31181475/268435456)), (257/4294967296), by norm_num⟩
  | 4 => ⟨((1089323861/4294967296), (195538669/2147483648)), (203/4294967296), by norm_num⟩
  | 5 => ⟨((-683113733/4294967296), (-122622073/2147483648)), (257/8589934592), by norm_num⟩
  | 6 => ⟨((356983193/4294967296), (512641067/17179869184)), (271/17179869184), by norm_num⟩
  | 7 => ⟨((-1279221413/34359738368), (-229626157/17179869184)), (245/34359738368), by norm_num⟩
  | 8 => ⟨((1002747835/68719476736), (359995743/68719476736)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((-698691119/137438953472), (-250836571/137438953472)), (17/17179869184), by norm_num⟩
  | 10 => ⟨((876296785/549755813888), (314598647/549755813888)), (43/137438953472), by norm_num⟩
  | 11 => ⟨((-499567909/1099511627776), (-89674749/549755813888)), (99/1099511627776), by norm_num⟩
  | 12 => ⟨((522130763/4398046511104), (187449771/4398046511104)), (209/8796093022208), by norm_num⟩
  | 13 => ⟨((-1007469531/35184372088832), (-361690875/35184372088832)), (51/8796093022208), by norm_num⟩
  | 14 => ⟨((451273555/70368744177664), (81005689/35184372088832)), (185/140737488355328), by norm_num⟩
  | 15 => ⟨((-1509296663/1125899906842624), (-270925727/562949953421312)), (39/140737488355328), by norm_num⟩
  | 16 => ⟨((1183097739/4503599627370496), (424743025/4503599627370496)), (123/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (224490931941/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111112415102751/39614081257132168796771975168), (530794458901/633825300114114700748351602688)), (23063/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888650724373765/39614081257132168796771975168), (298502445505/19807040628566084398385987584)), (207575/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472089485981889/618970019642690137449562112), (317071411015/1237940039285380274899124224)), (220557/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770024577521923/154742504910672534362390528), (633946191641/154742504910672534362390528)), (110283/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548460605297017/9671406556917033397649408), (74264465089/1208925819614629174706176)), (103395/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628916436893055/302231454903657293676544), (519642518293/604462909807314587353088)), (180951/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943119809043531/37778931862957161709568), (844027914937/75557863725914323419136)), (294061/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296375800956455/4722366482869645213696), (632678861155/4722366482869645213696)), (110281/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809924588301355/295147905179352825856), (434688973197/295147905179352825856)), (151649/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821477569704961/73786976294838206464), (1085889873367/73786976294838206464)), (47395/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227551553843269/1152921504606846976), (610241214459/4611686018427387904)), (426607/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591663699373299/1152921504606846976), (304763616297/288230376151711744)), (213337/576460752303423488), by norm_num⟩
  | 5 => ⟨((145575192287/17592186044416), (133133555313/18014398509481984)), (186707/72057594037927936), by norm_num⟩
  | 4 => ⟨((372150104246803/9007199254740992), (12456248733/281474976710656)), (280135/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485472271959391/9007199254740992), (1987407435593/9007199254740992)), (87575/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110204819343493/2251799813685248), (989522001071/1125899906842624)), (1401995/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204876691549753/2251799813685248), (736936259895/281474976710656)), (1052501/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079299745324933/1125899906842624), (2906364928163/562949953421312)), (2109085/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079299745324933/1125899906842624), (2906364928163/562949953421312)), (8045520786765670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069196640572959/2251799813685248), (22288581126785/2251799813685248)), (4065361/1125899906842624), by norm_num⟩
  | 2 => ⟨((950590263506473/1125899906842624), (40962306605047/2251799813685248)), (943983/140737488355328), by norm_num⟩
  | 3 => ⟨((802204854928505/1125899906842624), (17292109890443/562949953421312)), (26053469/2251799813685248), by norm_num⟩
  | 4 => ⟨((1141018943352299/2251799813685248), (12320646286375/281474976710656)), (1210213/70368744177664), by norm_num⟩
  | 5 => ⟨((573856134297969/2251799813685248), (199777486032773/4503599627370496)), (85274271/4503599627370496), by norm_num⟩
  | 6 => ⟨((567249539589225/9007199254740992), (407295658016457/18014398509481984)), (204114433/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-735009129/8388608)), (1/8388608), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45987547/16777216), (-1489971543/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((771544116529509/18014398509481984), (-27150627902325/562949953421312)), (138239723/9007199254740992), by norm_num⟩
  | 1 => ⟨((-292302219/2147483648), (329155567/2147483648)), (211/4294967296), by norm_num⟩
  | 2 => ⟨((928952187/4294967296), (-523037055/2147483648)), (169/2147483648), by norm_num⟩
  | 3 => ⟨((-984086685/4294967296), (138519993/536870912)), (45/536870912), by norm_num⟩
  | 4 => ⟨((781870115/4294967296), (-880447989/4294967296)), (9/134217728), by norm_num⟩
  | 5 => ⟨((-993930125/8589934592), (1119244441/8589934592)), (369/8589934592), by norm_num⟩
  | 6 => ⟨((526460573/8589934592), (-296418257/4294967296)), (197/8589934592), by norm_num⟩
  | 7 => ⟨((-478034297/17179869184), (1076609345/34359738368)), (45/4294967296), by norm_num⟩
  | 8 => ⟨((189902341/17179869184), (-855380613/68719476736)), (9/2147483648), by norm_num⟩
  | 9 => ⟨((-134115525/34359738368), (302049515/68719476736)), (205/137438953472), by norm_num⟩
  | 10 => ⟨((681962173/549755813888), (-383971847/274877906944)), (263/549755813888), by norm_num⟩
  | 11 => ⟨((-788113635/2199023255552), (443739345/1099511627776)), (153/1099511627776), by norm_num⟩
  | 12 => ⟨((834889185/8796093022208), (-940151683/8796093022208)), (163/4398046511104), by norm_num⟩
  | 13 => ⟨((-816407007/35184372088832), (919339279/35184372088832)), (321/35184372088832), by norm_num⟩
  | 14 => ⟨((741310119/140737488355328), (-834774205/140737488355328)), (147/70368744177664), by norm_num⟩
  | 15 => ⟨((-628246257/562949953421312), (11053989/8796093022208)), (251/562949953421312), by norm_num⟩
  | 16 => ⟨((249575053/1125899906842624), (-562082753/2251799813685248)), (401/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-17191018721/158456325028528675187087900672)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777741358281595/633825300114114700748351602688), (-1300627196571/633825300114114700748351602688)), (11541/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944293127142947/19807040628566084398385987584), (-1462860359143/39614081257132168796771975168)), (207755/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888289407799913/2475880078570760549798248448), (-388463688183/618970019642690137449562112)), (220759/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110622250013693/9671406556917033397649408), (-388341581823/38685626227668133590597632)), (220781/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774198135186645/4835703278458516698824704), (-363940547575/2417851639229258349412352)), (207005/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314444134269431/151115727451828646838272), (-1273273411891/604462909807314587353088)), (5661/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((235768498650345/9444732965739290427392), (-1034048800669/37778931862957161709568)), (294415/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296307007887403/4722366482869645213696), (-1550223472525/4722366482869645213696)), (220849/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809877235152815/295147905179352825856), (-66568044007/18446744073709551616)), (303729/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821359013455281/73786976294838206464), (-1330326804133/36893488147419103232)), (47469/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820278817158033/9223372036854775808), (-1495197137747/4611686018427387904)), (106837/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198941223675823/144115188075855872), (-2986846991945/1152921504606846976)), (427507/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192434471776439/144115188075855872), (-326188241157/18014398509481984)), (374247/144115188075855872), by norm_num⟩
  | 4 => ⟨((46513234387705/1125899906842624), (-3906302259729/36028797018963968)), (561729/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485249975502691/9007199254740992), (-152155768195/281474976710656)), (702789/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109980810257315/2251799813685248), (-4848206316213/2251799813685248)), (703735/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204196194957195/2251799813685248), (-14441157570525/2251799813685248)), (264495/281474976710656), by norm_num⟩
  | 0 => ⟨((2157205179386491/2251799813685248), (-7117759879315/562949953421312)), (4251085/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157205179386491/2251799813685248), (-7117759879315/562949953421312)), (16216602334029387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033112170452257/1125899906842624), (-54550030189971/2251799813685248)), (4126253/1125899906842624), by norm_num⟩
  | 2 => ⟨((1894621047228181/2251799813685248), (-100108899104251/2251799813685248)), (3886159/562949953421312), by norm_num⟩
  | 3 => ⟨((794823567167345/1125899906842624), (-84229701994401/1125899906842624)), (27540061/2251799813685248), by norm_num⟩
  | 4 => ⟨((69350065715241/140737488355328), (-59461548752033/562949953421312)), (43004145/2251799813685248), by norm_num⟩
  | 5 => ⟨((521646584099795/2251799813685248), (-234403064125871/2251799813685248)), (51466225/2251799813685248), by norm_num⟩
  | 6 => ⟨((771544116529509/18014398509481984), (-27150627902325/562949953421312)), (138239723/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1489971543/16777216)), (1/8388608), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-754555089/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-225926586027831/9007199254740992), (-128340018092321/2251799813685248)), (100083407/4503599627370496), by norm_num⟩
  | 1 => ⟨((86692527/1073741824), (787945903/4294967296)), (309/4294967296), by norm_num⟩
  | 2 => ⟨((-558104959/4294967296), (-1268150009/4294967296)), (125/1073741824), by norm_num⟩
  | 3 => ⟨((18713235/134217728), (1360672469/4294967296)), (269/2147483648), by norm_num⟩
  | 4 => ⟨((-240942319/2147483648), (-1094958929/4294967296)), (435/4294967296), by norm_num⟩
  | 5 => ⟨((620450725/8589934592), (1409814731/8589934592)), (281/4294967296), by norm_num⟩
  | 6 => ⟨((-332858973/8589934592), (-378168213/4294967296)), (303/8589934592), by norm_num⟩
  | 7 => ⟨((612246687/34359738368), (347793291/8589934592)), (35/2147483648), by norm_num⟩
  | 8 => ⟨((-492686515/68719476736), (-1119503417/68719476736)), (113/17179869184), by norm_num⟩
  | 9 => ⟨((88105373/34359738368), (800787219/137438953472)), (325/137438953472), by norm_num⟩
  | 10 => ⟨((-56720051/68719476736), (-128881731/68719476736)), (105/137438953472), by norm_num⟩
  | 11 => ⟨((265563347/1099511627776), (1206848839/2199023255552)), (247/1099511627776), by norm_num⟩
  | 12 => ⟨((-569876959/8796093022208), (-1294898851/8796093022208)), (133/2199023255552), by norm_num⟩
  | 13 => ⟨((141104859/8796093022208), (1282498033/35184372088832)), (529/35184372088832), by norm_num⟩
  | 14 => ⟨((-259542297/70368744177664), (-1179486261/140737488355328)), (489/140737488355328), by norm_num⟩
  | 15 => ⟨((445565027/562949953421312), (506215975/281474976710656)), (421/562949953421312), by norm_num⟩
  | 16 => ⟨((-350151/2199023255552), (-407361591/1125899906842624)), (341/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-1293090722713/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777683035594969/633825300114114700748351602688), (-3057067097565/633825300114114700748351602688)), (92501/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888520432536075/39614081257132168796771975168), (-1719185666435/19807040628566084398385987584)), (208167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888219189638081/2475880078570760549798248448), (-1826117278559/1237940039285380274899124224)), (110611/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769885464590271/154742504910672534362390528), (-3651070664109/154742504910672534362390528)), (27659/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548329806209875/9671406556917033397649408), (-1710821273901/4835703278458516698824704)), (207497/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628859022129039/302231454903657293676544), (-2992701520485/604462909807314587353088)), (181613/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886052307812877/75557863725914323419136), (-4860824059645/75557863725914323419136)), (147611/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324058673954233/1180591620717411303424), (-3643592665027/4722366482869645213696)), (221505/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619654147118363/590295810358705651712), (-312915664145/36893488147419103232)), (38089/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227654033832613/9223372036854775808), (-3126691384233/36893488147419103232)), (381105/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910067197211917/4611686018427387904), (-3514140853905/4611686018427387904)), (26815/576460752303423488), by norm_num⟩
  | 6 => ⟨((795691537980531/576460752303423488), (-877477830609/144115188075855872)), (214705/576460752303423488), by norm_num⟩
  | 5 => ⟨((149037941027333/18014398509481984), (-191651243755/4503599627370496)), (47019/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488221965835395/36028797018963968), (-2295069556131/9007199254740992)), (565063/36028797018963968), by norm_num⟩
  | 3 => ⟨((742494571027025/4503599627370496), (-2860548591911/2251799813685248)), (707793/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219413381042695/4503599627370496), (-11392592403133/2251799813685248)), (1419991/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203308007691837/2251799813685248), (-33930662816363/2251799813685248)), (535259/562949953421312), by norm_num⟩
  | 0 => ⟨((1077584546188123/1125899906842624), (-66878227396909/2251799813685248)), (2163239/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077584546188123/1125899906842624), (-66878227396909/2251799813685248)), (8252101902488326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060698775811653/2251799813685248), (-32004152359095/562949953421312)), (8538627/2251799813685248), by norm_num⟩
  | 2 => ⟨((939268927600003/1125899906842624), (-117152363520881/1125899906842624)), (8299417/1125899906842624), by norm_num⟩
  | 3 => ⟨((1542768476661271/2251799813685248), (-390931997351855/2251799813685248)), (7787265/562949953421312), by norm_num⟩
  | 4 => ⟨((494561446468251/1125899906842624), (-535676003139569/2251799813685248)), (26748805/1125899906842624), by norm_num⟩
  | 5 => ⟨((153525040900491/1125899906842624), (-235300400453863/1125899906842624)), (36225733/1125899906842624), by norm_num⟩
  | 6 => ⟨((-225926586027831/9007199254740992), (-128340018092321/2251799813685248)), (100083407/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-754555089/8388608)), (1/8388608), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47145793/16777216), (-1527498081/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1082474481708935/18014398509481984), (-32625397892049/9007199254740992)), (45015965/2251799813685248), by norm_num⟩
  | 1 => ⟨((1681712323/8589934592), (101372429/8589934592)), (561/8589934592), by norm_num⟩
  | 2 => ⟨((-1369795275/4294967296), (-41285145/2147483648)), (459/4294967296), by norm_num⟩
  | 3 => ⟨((371910437/1073741824), (11209249/536870912)), (125/1073741824), by norm_num⟩
  | 4 => ⟨((-1211720107/4294967296), (-73041631/4294967296)), (409/4294967296), by norm_num⟩
  | 5 => ⟨((789580217/4294967296), (47595337/4294967296)), (535/8589934592), by norm_num⟩
  | 6 => ⟨((-214377381/2147483648), (-103380135/17179869184)), (583/17179869184), by norm_num⟩
  | 7 => ⟨((1596485035/34359738368), (96234989/34359738368)), (545/34359738368), by norm_num⟩
  | 8 => ⟨((-162546949/8589934592), (-78385721/68719476736)), (223/34359738368), by norm_num⟩
  | 9 => ⟨((1882999651/274877906944), (113505887/274877906944)), (81/34359738368), by norm_num⟩
  | 10 => ⟨((-1226998929/549755813888), (-18490657/137438953472)), (53/68719476736), by norm_num⟩
  | 11 => ⟨((181712771/274877906944), (87628139/2199023255552)), (63/274877906944), by norm_num⟩
  | 12 => ⟨((-789383667/4398046511104), (-95166979/8796093022208)), (549/8796093022208), by norm_num⟩
  | 13 => ⟨((791350213/17592186044416), (95404063/35184372088832)), (69/4398046511104), by norm_num⟩
  | 14 => ⟨((-1473311651/140737488355328), (-88810185/140737488355328)), (129/35184372088832), by norm_num⟩
  | 15 => ⟨((1280051091/562949953421312), (77160575/562949953421312)), (225/281474976710656), by norm_num⟩
  | 16 => ⟨((-1042632507/2251799813685248), (-62849151/2251799813685248)), (23/140737488355328), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-2006924790223/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444405971305379/158456325028528675187087900672), (-4744416392799/633825300114114700748351602688)), (92667/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472113379888279/9903520314283042199192993792), (-667018238215/4951760157141521099596496896)), (104281/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236018449390389/309485009821345068724781056), (-5668026846337/2475880078570760549798248448)), (221667/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884906654418903/77371252455336267181195264), (-5666195505821/154742504910672534362390528)), (221745/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548261564406533/9671406556917033397649408), (-1327528248533/2417851639229258349412352)), (103985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257657737490249/604462909807314587353088), (-1161101036555/151115727451828646838272)), (182057/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885953194598727/75557863725914323419136), (-7543511589975/75557863725914323419136)), (147999/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648079693396595/2361183241434822606848), (-2827222698877/2361183241434822606848)), (27767/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809774508322247/295147905179352825856), (-7769683711217/590295810358705651712)), (305659/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113818655678671/4611686018427387904), (-2426085135857/18446744073709551616)), (382407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909990322319957/4611686018427387904), (-10906713933823/9223372036854775808)), (430669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795612638430413/576460752303423488), (-10893387146121/1152921504606846976)), (431243/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192160912346595/144115188075855872), (-9516734437893/144115188075855872)), (377985/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487998993201317/36028797018963968), (-7122588173007/18014398509481984)), (568275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484694668257077/9007199254740992), (-8877088075181/4503599627370496)), (89077/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109388734181219/2251799813685248), (-17675884858937/2251799813685248)), (716033/2251799813685248), by norm_num⟩
  | 1 => ⟨((550559450858469/562949953421312), (-26318625001015/1125899906842624)), (541309/562949953421312), by norm_num⟩
  | 0 => ⟨((1076284888842425/1125899906842624), (-6482450033333/140737488355328)), (2199677/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076284888842425/1125899906842624), (-6482450033333/140737488355328)), (8391101841453170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2052935144211313/2251799813685248), (-99148607738931/1125899906842624)), (4408125/1125899906842624), by norm_num⟩
  | 2 => ⟨((463542639902631/562949953421312), (-180784863814119/1125899906842624)), (8814029/1125899906842624), by norm_num⟩
  | 3 => ⟨((91793678108333/140737488355328), (-297722710580339/1125899906842624)), (17345769/1125899906842624), by norm_num⟩
  | 4 => ⟨((400240076997967/1125899906842624), (-388369338971757/1125899906842624)), (7950123/281474976710656), by norm_num⟩
  | 5 => ⟨((33258287793029/4503599627370496), (-1104474550101781/4503599627370496)), (178191101/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1082474481708935/18014398509481984), (-32625397892049/9007199254740992)), (45015965/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1527498081/16777216)), (1/8388608), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-1545191933/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-286035708950155/9007199254740992), (880125698536527/18014398509481984)), (95602159/4503599627370496), by norm_num⟩
  | 1 => ⟨((28095455/268435456), (-345796433/2147483648)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((-740784291/4294967296), (142461079/536870912)), (499/4294967296), by norm_num⟩
  | 3 => ⟨((813834725/4294967296), (-39127373/134217728)), (551/4294967296), by norm_num⟩
  | 4 => ⟨((-335283311/2147483648), (1031659507/4294967296)), (57/536870912), by norm_num⟩
  | 5 => ⟨((442015639/4294967296), (-680036287/4294967296)), (151/2147483648), by norm_num⟩
  | 6 => ⟨((-485603813/8589934592), (373548111/4294967296)), (167/4294967296), by norm_num⟩
  | 7 => ⟨((228638707/8589934592), (-703516363/17179869184)), (79/4294967296), by norm_num⟩
  | 8 => ⟨((-94194485/8589934592), (579668791/34359738368)), (523/68719476736), by norm_num⟩
  | 9 => ⟨((137977625/34359738368), (-849108343/137438953472)), (385/137438953472), by norm_num⟩
  | 10 => ⟨((-727602789/549755813888), (139926129/68719476736)), (509/549755813888), by norm_num⟩
  | 11 => ⟨((218005463/549755813888), (-670798101/1099511627776)), (307/1099511627776), by norm_num⟩
  | 12 => ⟨((-479006961/4398046511104), (736947037/4398046511104)), (339/4398046511104), by norm_num⟩
  | 13 => ⟨((121440677/4398046511104), (-747340681/17592186044416)), (345/17592186044416), by norm_num⟩
  | 14 => ⟨((-14294595/2199023255552), (351873281/35184372088832)), (327/70368744177664), by norm_num⟩
  | 15 => ⟨((201013987/140737488355328), (-618515697/281474976710656)), (577/562949953421312), by norm_num⟩
  | 16 => ⟨((-662509309/2251799813685248), (509631709/1125899906842624)), (477/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (2796919971219/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222197497662845/79228162514264337593543950336), (3305813773337/633825300114114700748351602688)), (185051/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888404479061639/39614081257132168796771975168), (3718122316687/39614081257132168796771975168)), (208225/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888095961891317/2475880078570760549798248448), (3949358884167/2475880078570760549798248448)), (27661/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884881103173667/77371252455336267181195264), (3948070052591/154742504910672534362390528)), (110671/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548214219260631/9671406556917033397649408), (3699946774207/9671406556917033397649408)), (103783/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628808436696863/302231454903657293676544), (3236085071003/604462909807314587353088)), (181679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942943922379709/37778931862957161709568), (5256073727017/75557863725914323419136)), (295337/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648055647905421/2361183241434822606848), (30779785161/36893488147419103232)), (110799/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809742193347817/295147905179352825856), (1353399952731/147573952589676412928)), (304853/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821019942446361/73786976294838206464), (845192497831/9223372036854775808)), (190649/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909947675160233/4611686018427387904), (3799615714595/4611686018427387904)), (429281/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795571907168945/576460752303423488), (3794932165423/576460752303423488)), (429681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596046965519911/72057594037927936), (828825745799/18014398509481984)), (376423/144115188075855872), by norm_num⟩
  | 4 => ⟨((743953543584323/18014398509481984), (4962444966151/18014398509481984)), (282769/18014398509481984), by norm_num⟩
  | 3 => ⟨((742297353382231/4503599627370496), (6184700112361/4503599627370496)), (708507/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218622031931341/4503599627370496), (12314473929225/2251799813685248)), (1421777/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202114900294475/2251799813685248), (36669782544677/2251799813685248)), (268077/281474976710656), by norm_num⟩
  | 0 => ⟨((1076379606830419/1125899906842624), (36125473963479/1125899906842624)), (2168635/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076379606830419/1125899906842624), (36125473963479/1125899906842624)), (8272686008933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2055756468399965/2251799813685248), (138146288937591/2251799813685248)), (2142835/562949953421312), by norm_num⟩
  | 2 => ⟨((934152812930537/1125899906842624), (252238343162595/2251799813685248)), (8350959/1125899906842624), by norm_num⟩
  | 3 => ⟨((760933922508473/1125899906842624), (418561466009983/2251799813685248)), (31456751/2251799813685248), by norm_num⟩
  | 4 => ⟨((950745276670205/2251799813685248), (282882711159503/1125899906842624)), (27107029/1125899906842624), by norm_num⟩
  | 5 => ⟨((259270857236383/2251799813685248), (955500217566507/4503599627370496)), (146045311/4503599627370496), by norm_num⟩
  | 6 => ⟨((-286035708950155/9007199254740992), (880125698536527/18014398509481984)), (95602159/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1545191933/16777216)), (1/8388608), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile043Terms3

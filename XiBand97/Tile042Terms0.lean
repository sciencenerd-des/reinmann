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
namespace Reinmann.XiBand97.Tile042Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35411/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35411/1280))
  have he : value ((69/80), (35411/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1286866721/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((36661148111063/70368744177664), (-99232363946611/562949953421312)), (3123297/140737488355328), by norm_num⟩
  | 1 => ⟨((-775499617/2147483648), (262384923/2147483648)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((537535373/4294967296), (-363742739/8589934592)), (49/8589934592), by norm_num⟩
  | 3 => ⟨((-496788171/17179869184), (42021209/4294967296)), (47/34359738368), by norm_num⟩
  | 4 => ⟨((43043415/8589934592), (-466030121/274877906944)), (17/68719476736), by norm_num⟩
  | 5 => ⟨((-763786797/1099511627776), (516843943/2199023255552)), (39/1099511627776), by norm_num⟩
  | 6 => ⟨((1411777773/17592186044416), (-477665229/17592186044416)), (37/8796093022208), by norm_num⟩
  | 7 => ⟨((-559182733/70368744177664), (47298901/17592186044416)), (61/140737488355328), by norm_num⟩
  | 8 => ⟨((1550383739/2251799813685248), (-262280799/1125899906842624)), (87/2251799813685248), by norm_num⟩
  | 9 => ⟨((-59702451/1125899906842624), (323198571/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((1059394191/288230376151711744), (-358438685/288230376151711744)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((-1068096141/4611686018427387904), (361382929/4611686018427387904)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((493565219/36893488147419103232), (-41748593/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 13 => ⟨((-842125145/1180591620717411303424), (35615901/147573952589676412928)), (57/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((1334209531/37778931862957161709568), (-451420551/37778931862957161709568)), (93/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-493228573/302231454903657293676544), (333760941/604462909807314587353088)), (71/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1367519979/19342813113834066795298816), (-231345455/9671406556917033397649408)), (101/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-106245084399/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781048288506081/633825300114114700748351602688), (-63020990051/79228162514264337593543950336)), (23063/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892306048369955/39614081257132168796771975168), (-141789571871/9903520314283042199192993792)), (12973/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892241072951829/2475880078570760549798248448), (-37660556221/154742504910672534362390528)), (27569/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773906972471853/154742504910672534362390528), (-9414492567/2417851639229258349412352)), (13785/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552099570823671/9671406556917033397649408), (-141206399111/2417851639229258349412352)), (3231/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((157627023640631/75557863725914323419136), (-494178443391/604462909807314587353088)), (11309/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((3694162196231/147573952589676412928), (-802957566369/75557863725914323419136)), (9189/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1300253092845483/4722366482869645213696), (-602146079819/4722366482869645213696)), (27569/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101573648583017/36893488147419103232), (-827833721691/590295810358705651712)), (18955/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828135958863445/73786976294838206464), (-517308236725/36893488147419103232)), (1481/1152921504606846976), by norm_num⟩
  | 7 => ⟨((913949421315245/4611686018427387904), (-581851010327/4611686018427387904)), (26661/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599144770458557/1152921504606846976), (-1163400199949/1152921504606846976)), (106659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199091909647567/144115188075855872), (-1017635721881/144115188075855872)), (2917/4503599627370496), by norm_num⟩
  | 4 => ⟨((374599581791447/9007199254740992), (-1525774914659/36028797018963968)), (140049/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497698706211919/9007199254740992), (-1906031509333/9007199254740992)), (175121/9007199254740992), by norm_num⟩
  | 2 => ⟨((4384374556595/8796093022208), (-952125939251/1125899906842624)), (350419/4503599627370496), by norm_num⟩
  | 1 => ⟨((2241305498184519/2251799813685248), (-1425966242133/562949953421312)), (131519/562949953421312), by norm_num⟩
  | 0 => ⟨((2230834161573235/2251799813685248), (-5686106080549/1125899906842624)), (526971/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2230834161573235/2251799813685248), (-5686106080549/1125899906842624)), (2010234837058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2210006279860331/2251799813685248), (-22532659632933/2251799813685248)), (262363/281474976710656), by norm_num⟩
  | 2 => ⟨((135547685194747/140737488355328), (-22114452176475/1125899906842624)), (4161903/2251799813685248), by norm_num⟩
  | 3 => ⟨((2087919434769257/2251799813685248), (-85195858954169/2251799813685248)), (8180353/2251799813685248), by norm_num⟩
  | 4 => ⟨((1932742513457091/2251799813685248), (-157991033298073/2251799813685248)), (1973627/281474976710656), by norm_num⟩
  | 5 => ⟨((823903713414307/1125899906842624), (-135605298901087/1125899906842624)), (14659663/1125899906842624), by norm_num⟩
  | 6 => ⟨((36661148111063/70368744177664), (-99232363946611/562949953421312)), (3123297/140737488355328), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1286866721/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-2039635497/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((454671167602523/2251799813685248), (745250092826931/2251799813685248)), (55521747/2251799813685248), by norm_num⟩
  | 1 => ⟨((-238183657/1073741824), (-390406089/1073741824)), (15/536870912), by norm_num⟩
  | 2 => ⟨((523342985/4294967296), (428904927/2147483648)), (17/1073741824), by norm_num⟩
  | 3 => ⟨((-191650345/4294967296), (-628266965/8589934592)), (103/17179869184), by norm_num⟩
  | 4 => ⟨((13159339/1073741824), (43138863/2147483648)), (59/34359738368), by norm_num⟩
  | 5 => ⟨((-740198991/274877906944), (-1213257857/274877906944)), (53/137438953472), by norm_num⟩
  | 6 => ⟨((542127805/1099511627776), (444299997/549755813888)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((-680672307/8796093022208), (-1115687855/8796093022208)), (103/8796093022208), by norm_num⟩
  | 8 => ⟨((747794961/70368744177664), (306427097/17592186044416)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((-365127437/281474976710656), (-1196958487/562949953421312)), (29/140737488355328), by norm_num⟩
  | 10 => ⟨((641813583/4503599627370496), (1051994643/4503599627370496)), (13/562949953421312), by norm_num⟩
  | 11 => ⟨((-32050195/2251799813685248), (-840533995/36028797018963968)), (85/36028797018963968), by norm_num⟩
  | 12 => ⟨((751162413/576460752303423488), (19237937/9007199254740992)), (127/576460752303423488), by norm_num⟩
  | 13 => ⟨((-507837697/4611686018427387904), (-832395185/4611686018427387904)), (11/576460752303423488), by norm_num⟩
  | 14 => ⟨((637619125/73786976294838206464), (1045119519/73786976294838206464)), (113/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-747195953/1180591620717411303424), (-1224726557/1180591620717411303424)), (135/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((12826229/295147905179352825856), (672749823/9444732965739290427392)), (19/2361183241434822606848), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (1332557674315/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780506825123529/633825300114114700748351602688), (197493260945/79228162514264337593543950336)), (23089/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472924218239907/9903520314283042199192993792), (1777287307219/39614081257132168796771975168)), (51955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118224611667383/154742504910672534362390528), (1888184991639/2475880078570760549798248448)), (6901/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886629822073941/77371252455336267181195264), (1887979388515/154742504910672534362390528)), (55215/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387873163966543/2417851639229258349412352), (1769762242853/9671406556917033397649408)), (51771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630242546955587/302231454903657293676544), (1548323550481/604462909807314587353088)), (45307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945273965566365/37778931862957161709568), (2515616293471/75557863725914323419136)), (18409/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649802842369031/2361183241434822606848), (943176987509/2361183241434822606848)), (27619/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((203036009062057/73786976294838206464), (2593154654521/590295810358705651712)), (75971/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913511449995245/36893488147419103232), (1620285189477/36893488147419103232)), (47495/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826646407191249/9223372036854775808), (911110408189/2305843009213693952)), (53451/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597892030230309/1152921504606846976), (910735487519/288230376151711744)), (106949/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598997709853005/72057594037927936), (3185887574557/144115188075855872)), (46817/72057594037927936), by norm_num⟩
  | 4 => ⟨((187094113672885/4503599627370496), (1193864844159/9007199254740992)), (70279/18014398509481984), by norm_num⟩
  | 3 => ⟨((46738773205847/281474976710656), (5963426123403/9007199254740992)), (43971/2251799813685248), by norm_num⟩
  | 2 => ⟨((140042517876781/281474976710656), (2977292365973/1125899906842624)), (176165/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117558709580641/1125899906842624), (8909793765947/1125899906842624)), (264949/1125899906842624), by norm_num⟩
  | 0 => ⟨((554605728103763/562949953421312), (17731375127359/1125899906842624)), (532711/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554605728103763/562949953421312), (17731375127359/1125899906842624)), (2032131199363326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((546245561191811/562949953421312), (34937109961639/1125899906842624)), (533205/562949953421312), by norm_num⟩
  | 2 => ⟨((1058989563449013/1125899906842624), (67800844893695/1125899906842624)), (533929/281474976710656), by norm_num⟩
  | 3 => ⟨((1983945347429085/2251799813685248), (255086217519279/2251799813685248)), (4274811/1125899906842624), by norm_num⟩
  | 4 => ⟨((1719056081136303/2251799813685248), (224743385875151/1125899906842624)), (1062643/140737488355328), by norm_num⟩
  | 5 => ⟨((1222628865754947/2251799813685248), (686289219558207/2251799813685248)), (8186827/562949953421312), by norm_num⟩
  | 6 => ⟨((454671167602523/2251799813685248), (745250092826931/2251799813685248)), (55521747/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-2039635497/67108864)), (1/33554432), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1286866721/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1082461891401897/4503599627370496), (-827179153943147/4503599627370496)), (4396559/140737488355328), by norm_num⟩
  | 1 => ⟨((-715546997/2147483648), (136698937/536870912)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((991958767/4294967296), (-379009931/2147483648)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((-916764563/8589934592), (700559107/8589934592)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((158863193/4294967296), (-242795285/8589934592)), (89/17179869184), by norm_num⟩
  | 5 => ⟨((-176184919/17179869184), (538537175/68719476736)), (101/68719476736), by norm_num⟩
  | 6 => ⟨((651317759/274877906944), (-497714033/274877906944)), (95/274877906944), by norm_num⟩
  | 7 => ⟨((-515953221/1099511627776), (394273233/1099511627776)), (153/2199023255552), by norm_num⟩
  | 8 => ⟨((715263041/8796093022208), (-68322345/1099511627776)), (27/2199023255552), by norm_num⟩
  | 9 => ⟨((-440695609/35184372088832), (673528047/70368744177664)), (135/70368744177664), by norm_num⟩
  | 10 => ⟨((244373535/140737488355328), (-746966507/562949953421312)), (19/70368744177664), by norm_num⟩
  | 11 => ⟨((-246380839/1125899906842624), (376551075/2251799813685248)), (155/4503599627370496), by norm_num⟩
  | 12 => ⟨((910816981/36028797018963968), (-21750443/1125899906842624)), (145/36028797018963968), by norm_num⟩
  | 13 => ⟨((-194255453/72057594037927936), (74221579/36028797018963968)), (63/144115188075855872), by norm_num⟩
  | 14 => ⟨((615531975/2305843009213693952), (-470367801/2305843009213693952)), (101/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-227548935/9223372036854775808), (347769723/18446744073709551616)), (19/4611686018427387904), by norm_num⟩
  | 16 => ⟨((630899611/295147905179352825856), (-241055603/147573952589676412928)), (107/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-849960675191/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780124477530581/633825300114114700748351602688), (-251835844961/158456325028528675187087900672)), (23075/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472816705171249/9903520314283042199192993792), (-566570188071/19807040628566084398385987584)), (103843/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891136964594525/2475880078570760549798248448), (-601907359427/1237940039285380274899124224)), (27585/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772802944054739/154742504910672534362390528), (-1203649449739/154742504910672534362390528)), (27587/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551064629117199/9671406556917033397649408), (-1128245789655/9671406556917033397649408)), (103461/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315027675016087/151115727451828646838272), (-493519764525/302231454903657293676544)), (90537/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889939783990505/75557863725914323419136), (-400902543059/18889465931478580854784)), (147139/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299149786819547/4722366482869645213696), (-601209884357/2361183241434822606848)), (110369/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623661557951731/590295810358705651712), (-826429769223/295147905179352825856)), (37945/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826240274241635/73786976294838206464), (-2065373184693/73786976294838206464)), (189761/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912883332177637/4611686018427387904), (-72580656209/288230376151711744)), (213529/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199626646975309/144115188075855872), (-290172094857/144115188075855872)), (213589/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197227420845001/144115188075855872), (-2029850653927/144115188075855872)), (186959/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495602906879499/36028797018963968), (-3042069859091/36028797018963968)), (140287/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494206728176335/9007199254740992), (-3797855879219/9007199254740992)), (350957/9007199254740992), by norm_num⟩
  | 2 => ⟨((279727838466583/562949953421312), (-7581534484699/4503599627370496)), (702631/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115428561685783/1125899906842624), (-354278693475/70368744177664)), (1031/2199023255552), by norm_num⟩
  | 0 => ⟨((2210006279860331/2251799813685248), (-22532659632933/2251799813685248)), (2118695/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210006279860331/2251799813685248), (-22532659632933/2251799813685248)), (8082180031783293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((135547685194747/140737488355328), (-22114452176475/1125899906842624)), (4201147/2251799813685248), by norm_num⟩
  | 2 => ⟨((2087919434769257/2251799813685248), (-85195858954169/2251799813685248)), (516093/140737488355328), by norm_num⟩
  | 3 => ⟨((1932742513457091/2251799813685248), (-157991033298073/2251799813685248)), (15937895/2251799813685248), by norm_num⟩
  | 4 => ⟨((823903713414307/1125899906842624), (-135605298901087/1125899906842624)), (14797893/1125899906842624), by norm_num⟩
  | 5 => ⟨((36661148111063/70368744177664), (-99232363946611/562949953421312)), (50443959/2251799813685248), by norm_num⟩
  | 6 => ⟨((1082461891401897/4503599627370496), (-827179153943147/4503599627370496)), (4396559/140737488355328), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1286866721/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1494005997/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((962436024880605/4503599627370496), (-580255430140845/4503599627370496)), (108074121/4503599627370496), by norm_num⟩
  | 1 => ⟨((-738611711/2147483648), (55663889/268435456)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((594374845/2147483648), (-716700587/4294967296)), (139/4294967296), by norm_num⟩
  | 3 => ⟨((-1275479213/8589934592), (768990065/8589934592)), (19/1073741824), by norm_num⟩
  | 4 => ⟨((1026402301/17179869184), (-618820883/17179869184)), (31/4294967296), by norm_num⟩
  | 5 => ⟨((-660772311/34359738368), (99595379/8589934592)), (81/34359738368), by norm_num⟩
  | 6 => ⟨((708981339/137438953472), (-427446877/137438953472)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((-81504389/68719476736), (196556917/274877906944)), (41/274877906944), by norm_num⟩
  | 8 => ⟨((524705015/2199023255552), (-158173077/1099511627776)), (67/2199023255552), by norm_num⟩
  | 9 => ⟨((-750649017/17592186044416), (452568439/17592186044416)), (97/17592186044416), by norm_num⟩
  | 10 => ⟨((483249195/70368744177664), (-582704643/140737488355328)), (127/140737488355328), by norm_num⟩
  | 11 => ⟨((-8838177/8796093022208), (85256995/140737488355328)), (151/1125899906842624), by norm_num⟩
  | 12 => ⟨((303455939/2251799813685248), (-365908907/4503599627370496)), (41/2251799813685248), by norm_num⟩
  | 13 => ⟨((-150274921/9007199254740992), (724809437/72057594037927936)), (165/72057594037927936), by norm_num⟩
  | 14 => ⟨((1105637281/576460752303423488), (-666591879/576460752303423488)), (77/288230376151711744), by norm_num⟩
  | 15 => ⟨((-949042431/4611686018427387904), (143045099/1152921504606846976)), (67/2305843009213693952), by norm_num⟩
  | 16 => ⟨((763712435/36893488147419103232), (-460444411/36893488147419103232)), (55/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-706733542145/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779827568233677/633825300114114700748351602688), (-418664988655/316912650057057350374175801344)), (92283/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472733211533999/9903520314283042199192993792), (-941880165799/39614081257132168796771975168)), (103823/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890782175797427/2475880078570760549798248448), (-250151480395/618970019642690137449562112)), (55159/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443112055449909/38685626227668133590597632), (-1000446482167/154742504910672534362390528)), (110325/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550732147689363/9671406556917033397649408), (-937749206815/9671406556917033397649408)), (103437/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629909924742475/302231454903657293676544), (-820361224175/604462909807314587353088)), (90515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236183410533799/9444732965739290427392), (-1332769573821/75557863725914323419136)), (36775/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324698881976797/1180591620717411303424), (-999299523453/4722366482869645213696)), (110337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811587320091695/295147905179352825856), (-686792902623/295147905179352825856)), (151733/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912815954635731/36893488147419103232), (-1716305964925/73786976294838206464)), (189695/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456270660414759/2305843009213693952), (-482478686061/2305843009213693952)), (213447/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596329637697647/1152921504606846976), (-1928753563095/1152921504606846976)), (106749/576460752303423488), by norm_num⟩
  | 5 => ⟨((598314934893561/72057594037927936), (-843176967255/72057594037927936)), (46717/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494707668907211/36028797018963968), (-2526922272775/36028797018963968)), (280415/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493089583643413/9007199254740992), (-3154092770073/9007199254740992)), (175359/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117797059450109/2251799813685248), (-3147262712585/2251799813685248)), (351017/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113764230384445/1125899906842624), (-1175963511881/281474976710656)), (1054551/2251799813685248), by norm_num⟩
  | 0 => ⟨((1101702828951609/1125899906842624), (-9339758355281/1125899906842624)), (2115123/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101702828951609/1125899906842624), (-9339758355281/1125899906842624)), (8068553933150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155896602989037/2251799813685248), (-36556138389221/2251799813685248)), (521803/281474976710656), by norm_num⟩
  | 2 => ⟨((1031742205343131/1125899906842624), (-69998455540093/2251799813685248)), (2032203/562949953421312), by norm_num⟩
  | 3 => ⟨((944370832504589/1125899906842624), (-16036141501263/281474976710656)), (3850849/562949953421312), by norm_num⟩
  | 4 => ⟨((1576910591327579/2251799813685248), (-53802524390211/562949953421312)), (27594927/2251799813685248), by norm_num⟩
  | 5 => ⟨((270931235995969/562949953421312), (-150709259385245/1125899906842624)), (43923479/2251799813685248), by norm_num⟩
  | 6 => ⟨((962436024880605/4503599627370496), (-580255430140845/4503599627370496)), (108074121/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1494005997/33554432)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1663251109/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((184122108298629/1125899906842624), (308119214558139/2251799813685248)), (6411721/562949953421312), by norm_num⟩
  | 1 => ⟨((-314619571/1073741824), (-526500245/2147483648)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((1127445191/4294967296), (117920225/536870912)), (85/4294967296), by norm_num⟩
  | 3 => ⟨((-673370199/4294967296), (-563425813/4294967296)), (13/1073741824), by norm_num⟩
  | 4 => ⟨((603258715/8589934592), (63095221/1073741824)), (3/536870912), by norm_num⟩
  | 5 => ⟨((-216178903/8589934592), (-361764671/17179869184)), (35/17179869184), by norm_num⟩
  | 6 => ⟨((516454129/68719476736), (864260367/137438953472)), (43/68719476736), by norm_num⟩
  | 7 => ⟨((-1057556087/549755813888), (-884883827/549755813888)), (45/274877906944), by norm_num⟩
  | 8 => ⟨((947443067/2199023255552), (49546843/137438953472)), (83/2199023255552), by norm_num⟩
  | 9 => ⟨((-754484483/8796093022208), (-631296179/8796093022208)), (17/2199023255552), by norm_num⟩
  | 10 => ⟨((540741887/35184372088832), (904904725/70368744177664)), (25/17592186044416), by norm_num⟩
  | 11 => ⟨((-704639561/281474976710656), (-147397419/70368744177664)), (67/281474976710656), by norm_num⟩
  | 12 => ⟨((210424101/562949953421312), (352134295/1125899906842624)), (81/2251799813685248), by norm_num⟩
  | 13 => ⟨((-928072309/18014398509481984), (-388270743/9007199254740992)), (91/18014398509481984), by norm_num⟩
  | 14 => ⟨((950218485/144115188075855872), (795071749/144115188075855872)), (95/144115188075855872), by norm_num⟩
  | 15 => ⟨((-908033583/1152921504606846976), (-759774579/1152921504606846976)), (93/1152921504606846976), by norm_num⟩
  | 16 => ⟨((406744443/4611686018427387904), (85083331/1152921504606846976)), (85/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (56723583545/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779584665987163/633825300114114700748351602688), (537504353005/316912650057057350374175801344)), (46153/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890659602603889/39614081257132168796771975168), (1209219364059/39614081257132168796771975168)), (25963/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236311485007095/309485009821345068724781056), (1284592973553/2475880078570760549798248448)), (55175/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772157954761889/154742504910672534362390528), (642182551099/77371252455336267181195264)), (13795/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550460052838385/9671406556917033397649408), (1203850223385/9671406556917033397649408)), (6467/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259581796987321/604462909807314587353088), (526563472799/302231454903657293676544)), (22637/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((59033765816991/2361183241434822606848), (855438832225/37778931862957161709568)), (36789/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298505494346531/4722366482869645213696), (320690364129/1180591620717411303424)), (55191/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811387962671769/295147905179352825856), (1763152455089/590295810358705651712)), (18975/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825133637681101/73786976294838206464), (2202974165671/73786976294838206464)), (47447/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824522253814683/9223372036854775808), (19351701651/72057594037927936)), (53391/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398942364868135/288230376151711744), (1237679336737/576460752303423488)), (53407/576460752303423488), by norm_num⟩
  | 5 => ⟨((299034987415669/36028797018963968), (2164073708713/144115188075855872)), (93499/144115188075855872), by norm_num⟩
  | 4 => ⟨((746986630183657/18014398509481984), (202648987379/2251799813685248)), (140321/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492172398353051/9007199254740992), (4046465767937/9007199254740992)), (175529/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233762224477531/4503599627370496), (8073420997367/4503599627370496)), (351441/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112393404759103/1125899906842624), (3015366222309/562949953421312)), (528125/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197947116645337/2251799813685248), (5982230123329/562949953421312)), (1060117/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197947116645337/2251799813685248), (5982230123329/562949953421312)), (4044025429732512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1072564023004391/1125899906842624), (46713301496055/2251799813685248)), (2092059/2251799813685248), by norm_num⟩
  | 2 => ⟨((510635112109447/562949953421312), (89000818413655/2251799813685248)), (4072709/2251799813685248), by norm_num⟩
  | 3 => ⟨((1849209824301097/2251799813685248), (161459975659601/2251799813685248)), (7710409/2251799813685248), by norm_num⟩
  | 4 => ⟨((1507020131153645/2251799813685248), (265186426792097/2251799813685248)), (3442377/562949953421312), by norm_num⟩
  | 5 => ⟨((977345242402267/2251799813685248), (354952763789733/2251799813685248)), (21673697/2251799813685248), by norm_num⟩
  | 6 => ⟨((184122108298629/1125899906842624), (308119214558139/2251799813685248)), (6411721/562949953421312), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1663251109/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-451586453/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-765523210481613/4503599627370496), (695186995278411/9007199254740992)), (18596085/562949953421312), by norm_num⟩
  | 1 => ⟨((710315411/2147483648), (-161262921/1073741824)), (139/2147483648), by norm_num⟩
  | 2 => ⟨((-1382209967/4294967296), (627606309/4294967296)), (273/4294967296), by norm_num⟩
  | 3 => ⟨((448276067/2147483648), (-407088495/4294967296)), (179/4294967296), by norm_num⟩
  | 4 => ⟨((-218076237/2147483648), (396078817/8589934592)), (11/536870912), by norm_num⟩
  | 5 => ⟨((1357941641/34359738368), (-77073379/4294967296)), (69/8589934592), by norm_num⟩
  | 6 => ⟨((-880810807/68719476736), (99985247/17179869184)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((489708197/137438953472), (-111178461/68719476736)), (101/137438953472), by norm_num⟩
  | 8 => ⟨((-952928151/1099511627776), (432686591/1099511627776)), (99/549755813888), by norm_num⟩
  | 9 => ⟨((206034729/1099511627776), (-187104273/2199023255552)), (173/4398046511104), by norm_num⟩
  | 10 => ⟨((-1282960225/35184372088832), (291270483/17592186044416)), (271/35184372088832), by norm_num⟩
  | 11 => ⟨((453913695/70368744177664), (-412208137/140737488355328)), (97/70368744177664), by norm_num⟩
  | 12 => ⟨((-1177700355/1125899906842624), (534746665/1125899906842624)), (253/1125899906842624), by norm_num⟩
  | 13 => ⟨((1410276353/9007199254740992), (-640350131/9007199254740992)), (305/9007199254740992), by norm_num⟩
  | 14 => ⟨((-98009681/4503599627370496), (178009117/18014398509481984)), (171/36028797018963968), by norm_num⟩
  | 15 => ⟨((406865137/144115188075855872), (-369482397/288230376151711744)), (179/288230376151711744), by norm_num⟩
  | 16 => ⟨((-791722999/2305843009213693952), (359489773/2305843009213693952)), (11/144115188075855872), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (3537069382437/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222421348481225/79228162514264337593543950336), (4188675298775/633825300114114700748351602688)), (23153/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890418518197227/39614081257132168796771975168), (4711538683131/39614081257132168796771975168)), (104215/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890235123229781/2475880078570760549798248448), (5005149869659/2475880078570760549798248448)), (110759/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55371891190855/4835703278458516698824704), (1251045581101/38685626227668133590597632)), (55397/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775108992023171/4835703278458516698824704), (2345196474335/4835703278458516698824704)), (51953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259369265302499/604462909807314587353088), (4103065890343/604462909807314587353088)), (45477/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472183447571595/18889465931478580854784), (833194346457/9444732965739290427392)), (147869/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81140267218439/295147905179352825856), (4997479778367/4722366482869645213696)), (55481/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811207415239107/295147905179352825856), (1717198655395/147573952589676412928)), (76335/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912339696861535/36893488147419103232), (4290941727937/36893488147419103232)), (23873/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824007280657657/9223372036854775808), (603060522327/576460752303423488)), (53765/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595249557838527/1152921504606846976), (9641905909439/1152921504606846976)), (13457/72057594037927936), by norm_num⟩
  | 5 => ⟨((298919875342301/36028797018963968), (263397606549/4503599627370496)), (188683/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493271544611937/36028797018963968), (12627199099705/36028797018963968)), (283593/36028797018963968), by norm_num⟩
  | 3 => ⟨((372818996244951/2251799813685248), (7878102031789/4503599627370496)), (11109/281474976710656), by norm_num⟩
  | 2 => ⟨((1115955909954257/2251799813685248), (15714523456213/2251799813685248)), (178493/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110934027808883/1125899906842624), (11733812553137/562949953421312)), (269615/562949953421312), by norm_num⟩
  | 0 => ⟨((1095770897882081/1125899906842624), (5814858123281/140737488355328)), (546757/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095770897882081/1125899906842624), (5814858123281/140737488355328)), (2085712435008811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1064526116896841/1125899906842624), (22637011578313/281474976710656)), (1109433/562949953421312), by norm_num⟩
  | 2 => ⟨((499607868349159/562949953421312), (42806096504951/281474976710656)), (4552723/1125899906842624), by norm_num⟩
  | 3 => ⟨((430373202896607/562949953421312), (75979267774027/281474976710656)), (9465655/1125899906842624), by norm_num⟩
  | 4 => ⟨((1152000786288275/2251799813685248), (232343501420807/562949953421312)), (2447887/140737488355328), by norm_num⟩
  | 5 => ⟨((102888757329359/1125899906842624), (950918974942783/2251799813685248)), (18100971/562949953421312), by norm_num⟩
  | 6 => ⟨((-765523210481613/4503599627370496), (695186995278411/9007199254740992)), (18596085/562949953421312), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-451586453/8388608)), (1/16777216), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-965150041/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((836278309653395/9007199254740992), (-1243513579006665/9007199254740992)), (141664345/4503599627370496), by norm_num⟩
  | 1 => ⟨((-12956499/67108864), (1233012101/4294967296)), (71/1073741824), by norm_num⟩
  | 2 => ⟨((107769129/536870912), (-320497073/1073741824)), (149/2147483648), by norm_num⟩
  | 3 => ⟨((-597598943/4294967296), (444303285/2147483648)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((310668017/4294967296), (-230975677/2147483648)), (219/8589934592), by norm_num⟩
  | 5 => ⟨((-32300799/1073741824), (768480669/17179869184)), (23/2147483648), by norm_num⟩
  | 6 => ⟨((89556831/8589934592), (-532670209/34359738368)), (129/34359738368), by norm_num⟩
  | 7 => ⟨((-425664445/137438953472), (316473303/68719476736)), (309/274877906944), by norm_num⟩
  | 8 => ⟨((442572165/549755813888), (-658087733/549755813888)), (81/274877906944), by norm_num⟩
  | 9 => ⟨((-409023531/2199023255552), (608202209/2199023255552)), (151/2199023255552), by norm_num⟩
  | 10 => ⟨((340216209/8796093022208), (-1011776751/17592186044416)), (127/8796093022208), by norm_num⟩
  | 11 => ⟨((-514516159/70368744177664), (765065675/70368744177664)), (97/35184372088832), by norm_num⟩
  | 12 => ⟨((356635425/281474976710656), (-1060606231/562949953421312)), (271/562949953421312), by norm_num⟩
  | 13 => ⟨((-114092695/562949953421312), (169651435/562949953421312)), (11/140737488355328), by norm_num⟩
  | 14 => ⟨((542283633/18014398509481984), (-403177419/9007199254740992)), (211/18014398509481984), by norm_num⟩
  | 15 => ⟨((-300705897/72057594037927936), (223569033/36028797018963968)), (59/36028797018963968), by norm_num⟩
  | 16 => ⟨((312650167/576460752303423488), (-929797469/1152921504606846976)), (31/144115188075855872), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-637470516099/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779201305067017/633825300114114700748351602688), (-188690800161/79228162514264337593543950336)), (138523/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890228350893499/39614081257132168796771975168), (-1697948640403/39614081257132168796771975168)), (155853/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890033708840741/2475880078570760549798248448), (-1803740265801/2475880078570760549798248448)), (82805/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771699821503019/154742504910672534362390528), (-901684465613/77371252455336267181195264)), (41407/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387507648311745/2417851639229258349412352), (-1690263927615/9671406556917033397649408)), (4853/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((157400757524265/75557863725914323419136), (-23102915641/9444732965739290427392)), (4247/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1888470009531929/75557863725914323419136), (-2401964080537/75557863725914323419136)), (220881/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40563990253983/147573952589676412928), (-1800826540661/4722366482869645213696)), (82847/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50692079671049/18446744073709551616), (-618771583943/147573952589676412928)), (113941/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824347079438271/73786976294838206464), (-3092283447587/73786976294838206464)), (284931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823637598102105/9223372036854775808), (-3476655220799/9223372036854775808)), (320657/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797442540912395/576460752303423488), (-1736976254871/576460752303423488)), (320793/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195366432285957/144115188075855872), (-3036670453421/144115188075855872)), (280849/144115188075855872), by norm_num⟩
  | 4 => ⟨((746406805517857/18014398509481984), (-2274468041591/18014398509481984)), (105395/9007199254740992), by norm_num⟩
  | 3 => ⟨((46585122963259/281474976710656), (-2837781334461/4503599627370496)), (263757/4503599627370496), by norm_num⟩
  | 2 => ⟨((2230868597208831/4503599627370496), (-707460025081/281474976710656)), (1056649/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220454636801823/2251799813685248), (-4224957184233/562949953421312)), (397259/562949953421312), by norm_num⟩
  | 0 => ⟨((1094657977640601/1125899906842624), (-16742005182205/1125899906842624)), (3194381/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094657977640601/1125899906842624), (-16742005182205/1125899906842624)), (12185596474654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128068020956223/2251799813685248), (-65109764813091/2251799813685248)), (6306485/2251799813685248), by norm_num⟩
  | 2 => ⟨((1004626208965247/1125899906842624), (-123064232893739/2251799813685248)), (3071153/562949953421312), by norm_num⟩
  | 3 => ⟨((1786104807851269/2251799813685248), (-219617308785397/2251799813685248)), (23265553/2251799813685248), by norm_num⟩
  | 4 => ⟨((697650520089805/1125899906842624), (-348396450452663/2251799813685248)), (41446167/2251799813685248), by norm_num⟩
  | 5 => ⟨((810678149515759/2251799813685248), (-431759454599043/2251799813685248)), (64188281/2251799813685248), by norm_num⟩
  | 6 => ⟨((836278309653395/9007199254740992), (-1243513579006665/9007199254740992)), (141664345/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-965150041/16777216)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile042Terms0

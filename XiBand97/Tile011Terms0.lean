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
namespace Reinmann.XiBand97.Tile011Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25029/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25029/1280))
  have he : value ((69/80), (25029/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-454787879/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((682271771446323/2251799813685248), (-1033612576509923/2251799813685248)), (38469407/2251799813685248), by norm_num⟩
  | 1 => ⟨((-451006655/2147483648), (683255809/2147483648)), (27/2147483648), by norm_num⟩
  | 2 => ⟨((625227983/8589934592), (-947193675/8589934592)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((-72229169/4294967296), (437696417/17179869184)), (39/34359738368), by norm_num⟩
  | 4 => ⟨((400523559/137438953472), (-606776075/137438953472)), (57/274877906944), by norm_num⟩
  | 5 => ⟨((-444194841/1099511627776), (672936201/1099511627776)), (33/1099511627776), by norm_num⟩
  | 6 => ⟨((205261601/4398046511104), (-1243850215/17592186044416)), (1/274877906944), by norm_num⟩
  | 7 => ⟨((-650406857/140737488355328), (492669297/70368744177664)), (53/140737488355328), by norm_num⟩
  | 8 => ⟨((450827679/1125899906842624), (-170746167/281474976710656)), (39/1125899906842624), by norm_num⟩
  | 9 => ⟨((-277768831/9007199254740992), (841615817/18014398509481984)), (25/9007199254740992), by norm_num⟩
  | 10 => ⟨((616110983/288230376151711744), (-933381809/288230376151711744)), (29/144115188075855872), by norm_num⟩
  | 11 => ⟨((-77646471/576460752303423488), (941048683/4611686018427387904)), (61/4611686018427387904), by norm_num⟩
  | 12 => ⟨((574084613/73786976294838206464), (-869713655/73786976294838206464)), (29/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-489754007/1180591620717411303424), (741956391/1180591620717411303424)), (51/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((775935107/37778931862957161709568), (-1175508527/37778931862957161709568)), (83/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-573693047/604462909807314587353088), (869120449/604462909807314587353088)), (63/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((198826859/4835703278458516698824704), (-602428389/9671406556917033397649408)), (45/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1286152336439/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781047183769667/633825300114114700748351602688), (-1525804117101/633825300114114700748351602688)), (1443/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1892304738430389/39614081257132168796771975168), (-1716435889741/39614081257132168796771975168)), (25977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946119799694815/1237940039285380274899124224), (-911800844565/1237940039285380274899124224)), (27603/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443476351738871/38685626227668133590597632), (-911738157109/77371252455336267181195264)), (13803/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776049002734347/4835703278458516698824704), (-854687917443/4835703278458516698824704)), (6471/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261014721776227/604462909807314587353088), (-1495570647127/604462909807314587353088)), (5663/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472852119238187/18889465931478580854784), (-2430052538595/75557863725914323419136)), (36815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300251007058953/4722366482869645213696), (-911160432049/2361183241434822606848)), (27617/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625175249210977/590295810358705651712), (-2505336066081/590295810358705651712)), (18991/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914065829308067/36893488147419103232), (-1565568704325/36893488147419103232)), (23745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827893468692143/9223372036854775808), (-880449293235/2305843009213693952)), (53445/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599138726662489/1152921504606846976), (-3520881680631/1152921504606846976)), (13367/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199085868206815/144115188075855872), (-3079741572705/144115188075855872)), (23405/72057594037927936), by norm_num⟩
  | 4 => ⟨((749193879971419/18014398509481984), (-2308776320665/18014398509481984)), (35133/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497682865971477/9007199254740992), (-2884168236173/4503599627370496)), (43961/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122380104721061/2251799813685248), (-5762930334997/2251799813685248)), (44029/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120613241132887/1125899906842624), (-4315440710873/562949953421312)), (132425/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115298834610937/1125899906842624), (-17207714211529/1125899906842624)), (66551/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115298834610937/1125899906842624), (-17207714211529/1125899906842624)), (253871918798351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1104534583845521/1125899906842624), (-34091385015309/1125899906842624)), (535533/1125899906842624), by norm_num⟩
  | 2 => ⟨((16914725514385/17592186044416), (-66888918867039/1125899906842624)), (1083173/1125899906842624), by norm_num⟩
  | 3 => ⟨((518440397992553/562949953421312), (-8039135242583/70368744177664)), (276453/140737488355328), by norm_num⟩
  | 4 => ⟨((117525666426297/140737488355328), (-236912710231575/1125899906842624)), (2289425/562949953421312), by norm_num⟩
  | 5 => ⟨((735285994706935/1125899906842624), (-98919358588127/281474976710656)), (9574293/1125899906842624), by norm_num⟩
  | 6 => ⟨((682271771446323/2251799813685248), (-1033612576509923/2251799813685248)), (38469407/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-454787879/33554432)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-360410867/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-762334621675705/2251799813685248), (-425405096469421/2251799813685248)), (77100251/2251799813685248), by norm_num⟩
  | 1 => ⟨((49919497/134217728), (445704715/2147483648)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-438737383/2147483648), (-489656677/4294967296)), (93/4294967296), by norm_num⟩
  | 3 => ⟨((1285339415/17179869184), (179314281/4294967296)), (139/17179869184), by norm_num⟩
  | 4 => ⟨((-353022419/17179869184), (-393993745/34359738368)), (79/34359738368), by norm_num⟩
  | 5 => ⟨((1241071257/274877906944), (43284637/17179869184)), (141/274877906944), by norm_num⟩
  | 6 => ⟨((-227242689/274877906944), (-126808091/274877906944)), (105/1099511627776), by norm_num⟩
  | 7 => ⟨((570632253/4398046511104), (636859095/8796093022208)), (67/4398046511104), by norm_num⟩
  | 8 => ⟨((-1253807211/70368744177664), (-174915307/17592186044416)), (75/35184372088832), by norm_num⟩
  | 9 => ⟨((1224398231/562949953421312), (341625077/281474976710656)), (149/562949953421312), by norm_num⟩
  | 10 => ⟨((-1076111155/4503599627370496), (-150125403/1125899906842624)), (67/2251799813685248), by norm_num⟩
  | 11 => ⟨((859802865/36028797018963968), (479795237/36028797018963968)), (109/36028797018963968), by norm_num⟩
  | 12 => ⟨((-1259453325/576460752303423488), (-702811925/576460752303423488)), (81/288230376151711744), by norm_num⟩
  | 13 => ⟨((851477477/4611686018427387904), (237574713/2305843009213693952)), (111/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-1069078423/73786976294838206464), (-596577141/73786976294838206464)), (71/36893488147419103232), by norm_num⟩
  | 15 => ⟨((1252802873/1180591620717411303424), (699100777/1180591620717411303424)), (169/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-172043079/2361183241434822606848), (-768040705/18889465931478580854784)), (47/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-3429262959353/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780499340059709/633825300114114700748351602688), (-4065903262783/633825300114114700748351602688)), (11575/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891688005225137/39614081257132168796771975168), (-4573730657467/39614081257132168796771975168)), (52101/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472895952948497/618970019642690137449562112), (-4859116135077/2475880078570760549798248448)), (13843/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773249047377767/154742504910672534362390528), (-2429292091893/77371252455336267181195264)), (13847/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551482060833711/9671406556917033397649408), (-2277178673617/4835703278458516698824704)), (51945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630237581457333/302231454903657293676544), (-3984497211173/604462909807314587353088)), (45469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890530555582065/75557863725914323419136), (-3236873706771/37778931862957161709568)), (1155/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1299591570565941/4722366482869645213696), (-2427191136199/2361183241434822606848)), (27735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812133453649479/295147905179352825856), (-6673266590415/590295810358705651712)), (38159/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826993807694025/73786976294838206464), (-4169659348305/36893488147419103232)), (23867/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826610056598397/9223372036854775808), (-9378618182433/9223372036854775808)), (107499/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597851156136923/1152921504606846976), (-9374721587121/1152921504606846976)), (107621/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1169877510765/140737488355328), (-4099247208439/72057594037927936)), (47153/72057594037927936), by norm_num⟩
  | 4 => ⟨((374170370344943/9007199254740992), (-768059965355/2251799813685248)), (70867/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495533715007511/9007199254740992), (-15345812015179/9007199254740992)), (88825/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120206558879663/2251799813685248), (-15322694255383/2251799813685248)), (178375/2251799813685248), by norm_num⟩
  | 1 => ⟨((558646071355133/562949953421312), (-22926118706055/1125899906842624)), (4209/17592186044416), by norm_num⟩
  | 0 => ⟨((1108414765217289/1125899906842624), (-45619781830147/1125899906842624)), (273013/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108414765217289/1125899906842624), (-45619781830147/1125899906842624)), (1041461946727561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((272338180286595/281474976710656), (-44911310018959/562949953421312)), (559671/562949953421312), by norm_num⟩
  | 2 => ⟨((523412978736169/562949953421312), (-86906939919021/562949953421312)), (2344615/1125899906842624), by norm_num⟩
  | 3 => ⟨((946472518504681/1125899906842624), (-323213244938785/1125899906842624)), (5083811/1125899906842624), by norm_num⟩
  | 4 => ⟨((702854154060559/1125899906842624), (-271704839917037/562949953421312)), (1433263/140737488355328), by norm_num⟩
  | 5 => ⟨((352979657490261/2251799813685248), (-1356915471817279/2251799813685248)), (3172971/140737488355328), by norm_num⟩
  | 6 => ⟨((-762334621675705/2251799813685248), (-425405096469421/2251799813685248)), (77100251/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-360410867/16777216)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-454787879/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-16732731539433/140737488355328), (-1252695162827009/4503599627370496)), (118361129/4503599627370496), by norm_num⟩
  | 1 => ⟨((353950369/2147483648), (828077431/2147483648)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-490679401/4294967296), (-1147959073/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((226742029/4294967296), (265234865/2147483648)), (53/4294967296), by norm_num⟩
  | 4 => ⟨((-628662393/34359738368), (-1470774391/34359738368)), (149/34359738368), by norm_num⟩
  | 5 => ⟨((87151113/17179869184), (407785249/34359738368)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((-80544731/68719476736), (-188436797/68719476736)), (79/274877906944), by norm_num⟩
  | 7 => ⟨((510439801/2199023255552), (298547279/549755813888)), (127/2199023255552), by norm_num⟩
  | 8 => ⟨((-353809909/8796093022208), (-827748819/8796093022208)), (45/4398046511104), by norm_num⟩
  | 9 => ⟨((27249149/4398046511104), (1020003129/70368744177664)), (113/70368744177664), by norm_num⟩
  | 10 => ⟨((-483524373/562949953421312), (-1131219669/562949953421312)), (127/562949953421312), by norm_num⟩
  | 11 => ⟨((487496081/4503599627370496), (1140511599/4503599627370496)), (65/2251799813685248), by norm_num⟩
  | 12 => ⟨((-450542045/36028797018963968), (-263514133/9007199254740992)), (123/36028797018963968), by norm_num⟩
  | 13 => ⟨((384359321/288230376151711744), (449610039/144115188075855872)), (53/144115188075855872), by norm_num⟩
  | 14 => ⟨((-152238617/1152921504606846976), (-1424667113/4611686018427387904)), (85/2305843009213693952), by norm_num⟩
  | 15 => ⟨((56279343/4611686018427387904), (131667199/4611686018427387904)), (1/288230376151711744), by norm_num⟩
  | 16 => ⟨((-624157887/590295810358705651712), (-365058991/147573952589676412928)), (45/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-2572304672877/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780120058584923/633825300114114700748351602688), (-3048604669363/633825300114114700748351602688)), (46251/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236407698583305/4951760157141521099596496896), (-1714652881329/19807040628566084398385987584)), (52041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236391384940399/309485009821345068724781056), (-455398959859/309485009821345068724781056)), (55305/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886398346156517/77371252455336267181195264), (-910672563509/38685626227668133590597632)), (55317/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551058378665299/9671406556917033397649408), (-1707244679427/4835703278458516698824704)), (25937/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315026210408985/151115727451828646838272), (-1493572722723/302231454903657293676544)), (22701/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944964767240457/37778931862957161709568), (-4853112477641/75557863725914323419136)), (18451/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649570730830735/2361183241434822606848), (-454870046123/590295810358705651712)), (55375/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623649074708629/590295810358705651712), (-625268789787/73786976294838206464)), (4761/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1826223117083643/73786976294838206464), (-6250557690823/73786976294838206464)), (95273/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456436307214267/2305843009213693952), (-109827320199/144115188075855872)), (107255/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798494537958993/576460752303423488), (-878160943167/144115188075855872)), (53673/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197203339767851/144115188075855872), (-383938018703/9007199254740992)), (5877/9007199254740992), by norm_num⟩
  | 4 => ⟨((1495560807293355/36028797018963968), (-1150784563465/4503599627370496)), (70627/18014398509481984), by norm_num⟩
  | 3 => ⟨((373535915837683/2251799813685248), (-11493434253591/9007199254740992)), (176929/9007199254740992), by norm_num⟩
  | 2 => ⟨((69927041918985/140737488355328), (-11471820264853/2251799813685248)), (2773/35184372088832), by norm_num⟩
  | 1 => ⟨((278817909642717/281474976710656), (-17153706444227/1125899906842624)), (133783/562949953421312), by norm_num⟩
  | 0 => ⟨((69033411490345/70368744177664), (-17045692507655/562949953421312)), (270291/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((69033411490345/70368744177664), (-17045692507655/562949953421312)), (1031078340770530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((541271216460319/562949953421312), (-66888918867041/1125899906842624)), (1093385/1125899906842624), by norm_num⟩
  | 2 => ⟨((518440397992551/562949953421312), (-32156540970333/281474976710656)), (2232475/1125899906842624), by norm_num⟩
  | 3 => ⟨((14690708303287/17592186044416), (-118456355115791/562949953421312)), (1155505/281474976710656), by norm_num⟩
  | 4 => ⟨((735285994706919/1125899906842624), (-98919358588129/281474976710656)), (604035/70368744177664), by norm_num⟩
  | 5 => ⟨((341135885723135/1125899906842624), (-516806288254961/1125899906842624)), (38832099/2251799813685248), by norm_num⟩
  | 6 => ⟨((-16732731539433/140737488355328), (-1252695162827009/4503599627370496)), (118361129/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-454787879/16777216)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1055984753/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((280533041536511/1125899906842624), (-30817478386259/2251799813685248)), (72249309/4503599627370496), by norm_num⟩
  | 1 => ⟨((-430584443/1073741824), (47301119/2147483648)), (113/4294967296), by norm_num⟩
  | 2 => ⟨((692998927/2147483648), (-38064107/2147483648)), (93/4294967296), by norm_num⟩
  | 3 => ⟨((-1487118329/8589934592), (81682423/8589934592)), (51/4294967296), by norm_num⟩
  | 4 => ⟨((598356155/8589934592), (-32865697/8589934592)), (21/4294967296), by norm_num⟩
  | 5 => ⟨((-770413665/34359738368), (42316239/34359738368)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((413310987/68719476736), (-45403573/137438953472)), (15/34359738368), by norm_num⟩
  | 7 => ⟨((-760226711/549755813888), (1304897/17179869184)), (7/68719476736), by norm_num⟩
  | 8 => ⟨((1223537691/4398046511104), (-67204823/4398046511104)), (23/1099511627776), by norm_num⟩
  | 9 => ⟨((-218800883/4398046511104), (96143991/35184372088832)), (67/17592186044416), by norm_num⟩
  | 10 => ⟨((1126868597/140737488355328), (-30947557/70368744177664)), (11/17592186044416), by norm_num⟩
  | 11 => ⟨((-1319000031/1125899906842624), (36224125/562949953421312)), (105/1125899906842624), by norm_num⟩
  | 12 => ⟨((707616219/4503599627370496), (-38866987/4503599627370496)), (115/9007199254740992), by norm_num⟩
  | 13 => ⟨((-1401679225/72057594037927936), (76989541/72057594037927936)), (29/18014398509481984), by norm_num⟩
  | 14 => ⟨((644547339/288230376151711744), (-70805649/576460752303423488)), (27/144115188075855872), by norm_num⟩
  | 15 => ⟨((-553258093/2305843009213693952), (7597153/576460752303423488)), (95/4611686018427387904), by norm_num⟩
  | 16 => ⟨((1780869101/73786976294838206464), (-97817169/73786976294838206464)), (155/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-35738133779/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222478492356985/79228162514264337593543950336), (-84684280459/633825300114114700748351602688)), (92209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945466642371305/19807040628566084398385987584), (-95258097655/39614081257132168796771975168)), (12967/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890782669139645/2475880078570760549798248448), (-50598697315/1237940039285380274899124224)), (27555/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772448745864365/154742504910672534362390528), (-101181272479/154742504910672534362390528)), (27555/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48460395988401/302231454903657293676544), (-740939975/75557863725914323419136)), (25833/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629910170272575/302231454903657293676544), (-41484077571/302231454903657293676544)), (90417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236183517919965/9444732965739290427392), (-134791156937/75557863725914323419136)), (9183/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298796225667959/4722366482869645213696), (-50532646559/2361183241434822606848)), (55099/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623175686388433/590295810358705651712), (-135663255/576460752303423488)), (151523/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825633347095041/73786976294838206464), (-86790293755/36893488147419103232)), (94703/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228135554734569/1152921504606846976), (-1524876455/72057594037927936)), (213087/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798165828491547/576460752303423488), (-97533393607/576460752303423488)), (53273/288230376151711744), by norm_num⟩
  | 5 => ⟨((598315943624949/72057594037927936), (-170551460215/144115188075855872)), (186461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494711195369905/36028797018963968), (-255563471209/36028797018963968)), (34963/4503599627370496), by norm_num⟩
  | 3 => ⟨((1493094865152739/9007199254740992), (-9968542679/281474976710656)), (87413/2251799813685248), by norm_num⟩
  | 2 => ⟨((2235607294070235/4503599627370496), (-636605949695/4503599627370496)), (699367/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227554725471589/2251799813685248), (-951464441883/2251799813685248)), (524609/1125899906842624), by norm_num⟩
  | 0 => ⟨((2203484025030383/2251799813685248), (-1889195691185/2251799813685248)), (524779/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203484025030383/2251799813685248), (-1889195691185/2251799813685248)), (2001873018504905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2156203340099577/2251799813685248), (-462165031321/281474976710656)), (1027919/562949953421312), by norm_num⟩
  | 2 => ⟨((1032329593737455/1125899906842624), (-3540356573991/1125899906842624)), (3943873/1125899906842624), by norm_num⟩
  | 3 => ⟨((1893049017065827/2251799813685248), (-1623063844975/281474976710656)), (14514043/2251799813685248), by norm_num⟩
  | 4 => ⟨((1591378577134527/2251799813685248), (-21831705626347/2251799813685248)), (24570793/2251799813685248), by norm_num⟩
  | 5 => ⟨((1124437943818959/2251799813685248), (-3857193302101/281474976710656)), (17602745/1125899906842624), by norm_num⟩
  | 6 => ⟨((280533041536511/1125899906842624), (-30817478386259/2251799813685248)), (72249309/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1055984753/33554432)), (1/16777216), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1175609613/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-852494475534109/4503599627370496), (221030644330639/2251799813685248)), (85333983/4503599627370496), by norm_num⟩
  | 1 => ⟨((728352093/2147483648), (-23605451/134217728)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((-81564485/268435456), (338362323/2147483648)), (135/4294967296), by norm_num⟩
  | 3 => ⟨((389717169/2147483648), (-404175931/4294967296)), (41/2147483648), by norm_num⟩
  | 4 => ⟨((-174569857/2147483648), (181046513/4294967296)), (149/17179869184), by norm_num⟩
  | 5 => ⟨((500459511/17179869184), (-519026887/34359738368)), (109/34359738368), by norm_num⟩
  | 6 => ⟨((-1195604091/137438953472), (619980893/137438953472)), (33/34359738368), by norm_num⟩
  | 7 => ⟨((612067129/274877906944), (-634775221/549755813888)), (137/549755813888), by norm_num⟩
  | 8 => ⟨((-548338537/1099511627776), (568682257/2199023255552)), (125/2199023255552), by norm_num⟩
  | 9 => ⟨((873325125/8796093022208), (-452863031/8796093022208)), (51/4398046511104), by norm_num⟩
  | 10 => ⟨((-625915425/35184372088832), (649137299/70368744177664)), (37/17592186044416), by norm_num⟩
  | 11 => ⟨((815629011/281474976710656), (-105736173/70368744177664)), (49/140737488355328), by norm_num⟩
  | 12 => ⟨((-974274003/2251799813685248), (505210105/2251799813685248)), (119/2251799813685248), by norm_num⟩
  | 13 => ⟨((537127591/9007199254740992), (-278527689/9007199254740992)), (133/18014398509481984), by norm_num⟩
  | 14 => ⟨((-549944827/72057594037927936), (285174071/72057594037927936)), (69/72057594037927936), by norm_num⟩
  | 15 => ⟨((262765027/288230376151711744), (-545027565/1152921504606846976)), (133/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-941623451/9223372036854775808), (244139575/4611686018427387904)), (121/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (1734567544047/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111223516312265/39614081257132168796771975168), (4109126871221/633825300114114700748351602688)), (46303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945324829865455/19807040628566084398385987584), (577764190995/4951760157141521099596496896)), (52103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890480696648901/2475880078570760549798248448), (4910218599253/2475880078570760549798248448)), (55375/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886073037604203/77371252455336267181195264), (2454672180257/77371252455336267181195264)), (1731/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1550448176454177/9671406556917033397649408), (4601581463965/9671406556917033397649408)), (12987/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629785333121987/302231454903657293676544), (503181864005/75557863725914323419136)), (1421/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1889061034075413/75557863725914323419136), (6539622613959/75557863725914323419136)), (36963/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298489679601599/4722366482869645213696), (4903193056125/4722366482869645213696)), (27737/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622752214267201/590295810358705651712), (6739414129945/590295810358705651712)), (76325/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912550526444157/36893488147419103232), (4210276609859/36893488147419103232)), (95477/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824481549721505/9223372036854775808), (9468015082361/9223372036854775808)), (107511/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595723704339253/1152921504606846976), (4730815539253/576460752303423488)), (107635/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149511780090547/18014398509481984), (8271745346645/144115188075855872)), (5895/9007199254740992), by norm_num⟩
  | 4 => ⟨((746946686805251/18014398509481984), (1549156842961/4503599627370496)), (141759/36028797018963968), by norm_num⟩
  | 3 => ⟨((746026387927161/4503599627370496), (15466433703745/9007199254740992)), (88843/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116731947177361/2251799813685248), (7714366899361/1125899906842624)), (44605/562949953421312), by norm_num⟩
  | 1 => ⟨((1112096162612547/1125899906842624), (5762214833865/281474976710656)), (269469/1125899906842624), by norm_num⟩
  | 0 => ⟨((549043631637251/562949953421312), (45720809657057/1125899906842624)), (273157/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549043631637251/562949953421312), (45720809657057/1125899906842624)), (1042011263133811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1069105022581941/1125899906842624), (89182774500451/1125899906842624)), (138751/140737488355328), by norm_num⟩
  | 2 => ⟨((1008110912119461/1125899906842624), (42342019733177/281474976710656)), (2283879/1125899906842624), by norm_num⟩
  | 3 => ⟨((438583420680139/562949953421312), (303298379365865/1125899906842624)), (2388507/562949953421312), by norm_num⟩
  | 4 => ⟨((1203360541268251/2251799813685248), (945175605046867/2251799813685248)), (20034105/2251799813685248), by norm_num⟩
  | 5 => ⟨((246345019008535/2251799813685248), (1010202612834683/2251799813685248)), (1194711/70368744177664), by norm_num⟩
  | 6 => ⟨((-852494475534109/4503599627370496), (221030644330639/2251799813685248)), (85333983/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1175609613/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1276750991/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1578943760606119/9007199254740992), (-578208182570571/9007199254740992)), (140787233/9007199254740992), by norm_num⟩
  | 1 => ⟨((-732536957/2147483648), (268254559/2147483648)), (133/4294967296), by norm_num⟩
  | 2 => ⟨((1425451099/4294967296), (-521999269/4294967296)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((-57787495/268435456), (84646973/1073741824)), (87/4294967296), by norm_num⟩
  | 4 => ⟨((112449273/1073741824), (-41178851/1073741824)), (43/4294967296), by norm_num⟩
  | 5 => ⟨((-700211781/17179869184), (256417101/17179869184)), (17/4294967296), by norm_num⟩
  | 6 => ⟨((908366141/68719476736), (-332643093/68719476736)), (45/34359738368), by norm_num⟩
  | 7 => ⟨((-505028255/137438953472), (46235255/34359738368)), (51/137438953472), by norm_num⟩
  | 8 => ⟨((982739607/1099511627776), (-22492413/68719476736)), (101/1099511627776), by norm_num⟩
  | 9 => ⟨((-424960661/2199023255552), (155620319/2199023255552)), (89/4398046511104), by norm_num⟩
  | 10 => ⟨((1323096421/35184372088832), (-484517053/35184372088832)), (35/8796093022208), by norm_num⟩
  | 11 => ⟨((-936227911/140737488355328), (342846055/140737488355328)), (101/140737488355328), by norm_num⟩
  | 12 => ⟨((303635899/281474976710656), (-444765079/1125899906842624)), (133/1125899906842624), by norm_num⟩
  | 13 => ⟨((-727197757/4503599627370496), (66574837/1125899906842624)), (161/9007199254740992), by norm_num⟩
  | 14 => ⟨((808606569/36028797018963968), (-148055601/18014398509481984)), (91/36028797018963968), by norm_num⟩
  | 15 => ⟨((-52449191/18014398509481984), (76827439/72057594037927936)), (3/9007199254740992), by norm_num⟩
  | 16 => ⟨((816491305/2305843009213693952), (-298998587/2305843009213693952)), (95/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-457259414383/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889690005218995/316912650057057350374175801344), (-270748323975/316912650057057350374175801344)), (92253/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945214712336463/19807040628566084398385987584), (-76136709829/4951760157141521099596496896)), (103789/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890247390263423/2475880078570760549798248448), (-161762808197/618970019642690137449562112)), (13785/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771913548475423/154742504910672534362390528), (-646926617539/154742504910672534362390528)), (27571/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550231010640345/9671406556917033397649408), (-303180666869/4835703278458516698824704)), (25849/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629690736862605/302231454903657293676544), (-530433834503/604462909807314587353088)), (22619/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888755147009523/75557863725914323419136), (-430853468827/37778931862957161709568)), (147033/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649130810159429/2361183241434822606848), (-646063245281/4722366482869645213696)), (110283/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622440834568643/590295810358705651712), (-55499034723/36893488147419103232)), (151651/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912357563996587/36893488147419103232), (-277363086693/18446744073709551616)), (189583/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912025958238019/4611686018427387904), (-623703919067/4611686018427387904)), (213307/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797649864563709/576460752303423488), (-1246500911865/1152921504606846976)), (213339/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195729617679143/144115188075855872), (-136208610423/18014398509481984)), (186709/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493359124532945/36028797018963968), (-1632466687935/36028797018963968)), (280137/36028797018963968), by norm_num⟩
  | 3 => ⟨((186425888477729/1125899906842624), (-2037024171027/9007199254740992)), (175151/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116119381645453/2251799813685248), (-4063390451973/4503599627370496)), (350497/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222519354880309/2251799813685248), (-758563711975/281474976710656)), (526237/1125899906842624), by norm_num⟩
  | 0 => ⟨((274185347716781/281474976710656), (-12031126922687/2251799813685248)), (527227/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274185347716781/281474976710656), (-12031126922687/2251799813685248)), (2011211397411155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1068305880591499/1125899906842624), (-11719545223065/1125899906842624)), (4131119/2251799813685248), by norm_num⟩
  | 2 => ⟨((1013536016683985/1125899906842624), (-44480185151693/2251799813685248)), (7925597/2251799813685248), by norm_num⟩
  | 3 => ⟨((911946638557965/1125899906842624), (-40041099040889/1125899906842624)), (7291185/1125899906842624), by norm_num⟩
  | 4 => ⟨((1474453238552033/2251799813685248), (-16216071007993/281474976710656)), (24659809/2251799813685248), by norm_num⟩
  | 5 => ⟨((478990813968995/1125899906842624), (-42472404996241/562949953421312)), (35135289/2251799813685248), by norm_num⟩
  | 6 => ⟨((1578943760606119/9007199254740992), (-578208182570571/9007199254740992)), (140787233/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1276750991/33554432)), (1/16777216), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1364363637/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-737242323751507/4503599627370496), (-33443622488197/1125899906842624)), (126654891/4503599627370496), by norm_num⟩
  | 1 => ⟨((731016309/2147483648), (33161191/536870912)), (127/2147483648), by norm_num⟩
  | 2 => ⟨((-1520105681/4294967296), (-275827033/4294967296)), (267/4294967296), by norm_num⟩
  | 3 => ⟨((1053656967/4294967296), (95594365/2147483648)), (187/4294967296), by norm_num⟩
  | 4 => ⟨((-547754517/4294967296), (-99391447/4294967296)), (49/2147483648), by norm_num⟩
  | 5 => ⟨((455609399/8589934592), (165342963/17179869184)), (165/17179869184), by norm_num⟩
  | 6 => ⟨((-1263217481/68719476736), (-229214017/68719476736)), (231/68719476736), by norm_num⟩
  | 7 => ⟨((1501021089/274877906944), (272364085/274877906944)), (277/274877906944), by norm_num⟩
  | 8 => ⟨((-390160701/274877906944), (-70795649/274877906944)), (291/1099511627776), by norm_num⟩
  | 9 => ⟨((1442340213/4398046511104), (261716291/4398046511104)), (17/274877906944), by norm_num⟩
  | 10 => ⟨((-1199704863/17592186044416), (-217689491/17592186044416)), (229/17592186044416), by norm_num⟩
  | 11 => ⟨((453584751/35184372088832), (329216415/140737488355328)), (349/140737488355328), by norm_num⟩
  | 12 => ⟨((-1257603965/562949953421312), (-114097715/281474976710656)), (61/140737488355328), by norm_num⟩
  | 13 => ⟨((1609300879/4503599627370496), (292011727/4503599627370496)), (315/4503599627370496), by norm_num⟩
  | 14 => ⟨((-956127743/18014398509481984), (-173491805/18014398509481984)), (189/18014398509481984), by norm_num⟩
  | 15 => ⟨((1060379599/144115188075855872), (192408569/144115188075855872)), (211/144115188075855872), by norm_num⟩
  | 16 => ⟨((-551249347/576460752303423488), (-100025593/576460752303423488)), (221/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-964614252329/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889595681219661/316912650057057350374175801344), (-2284200828393/316912650057057350374175801344)), (92649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945108298133067/19807040628566084398385987584), (-5138610335173/39614081257132168796771975168)), (26065/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890020488059417/2475880078570760549798248448), (-5458770883649/2475880078570760549798248448)), (110809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442921444572165/38685626227668133590597632), (-5457642851829/154742504910672534362390528)), (110847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550016554381193/9671406556917033397649408), (-5115341673485/9671406556917033397649408)), (12995/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157399112922119/75557863725914323419136), (-2237362750903/302231454903657293676544)), (22751/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888446994338991/75557863725914323419136), (-7269181903671/75557863725914323419136)), (147957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162253624617619/590295810358705651712), (-5449920351553/4722366482869645213696)), (55517/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622118527840829/590295810358705651712), (-3745222881273/295147905179352825856)), (76389/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824308574299539/73786976294838206464), (-4679132695999/36893488147419103232)), (191131/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823589503574777/9223372036854775808), (-10521460268887/9223372036854775808)), (215243/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594831026191973/1152921504606846976), (-10513225570087/1152921504606846976)), (215519/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298828110002151/36028797018963968), (-2297452318739/36028797018963968)), (188889/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492719267010483/36028797018963968), (-860386880953/2251799813685248)), (283955/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490582703482291/9007199254740992), (-1073457899861/562949953421312)), (5563/140737488355328), by norm_num⟩
  | 2 => ⟨((557629128569467/1125899906842624), (-8563360369605/1125899906842624)), (357667/2251799813685248), by norm_num⟩
  | 1 => ⟨((554938363289643/562949953421312), (-25568607217023/1125899906842624)), (540597/1125899906842624), by norm_num⟩
  | 0 => ⟨((546806821750663/562949953421312), (-25325784773061/562949953421312)), (1097637/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546806821750663/562949953421312), (-25325784773061/562949953421312)), (4187152866843795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1059974525712057/1125899906842624), (-98398174089445/1125899906842624)), (2231083/1125899906842624), by norm_num⟩
  | 2 => ⟨((989309784755189/1125899906842624), (-185273233042323/1125899906842624)), (4590863/1125899906842624), by norm_num⟩
  | 3 => ⟨((209700630045085/281474976710656), (-162796551618881/562949953421312)), (4789369/562949953421312), by norm_num⟩
  | 4 => ⟨((1061513186657403/2251799813685248), (-242568912111427/562949953421312)), (19812491/1125899906842624), by norm_num⟩
  | 5 => ⟨((164646440020291/4503599627370496), (-1829577192889221/4503599627370496)), (71506887/2251799813685248), by norm_num⟩
  | 6 => ⟨((-737242323751507/4503599627370496), (-33443622488197/1125899906842624)), (126654891/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1364363637/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile011Terms0

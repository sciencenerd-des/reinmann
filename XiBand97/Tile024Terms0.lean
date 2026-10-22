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
namespace Reinmann.XiBand97.Tile024Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5865/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5865/256))
  have he : value ((69/80), (5865/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1065696157/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1220181129814497/2251799813685248), (212150274278673/2251799813685248)), (25632963/562949953421312), by norm_num⟩
  | 1 => ⟨((806584463/2147483648), (-280478219/4294967296)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((-1118163493/8589934592), (194412687/8589934592)), (97/8589934592), by norm_num⟩
  | 3 => ⟨((1033402497/34359738368), (-89837737/17179869184)), (23/8589934592), by norm_num⟩
  | 4 => ⟨((-716300027/137438953472), (31135387/34359738368)), (65/137438953472), by norm_num⟩
  | 5 => ⟨((1588804301/2199023255552), (-276241993/2199023255552)), (73/1099511627776), by norm_num⟩
  | 6 => ⟨((-734183481/8796093022208), (255301811/17592186044416)), (137/17592186044416), by norm_num⟩
  | 7 => ⟨((1163193623/140737488355328), (-101120989/70368744177664)), (111/140737488355328), by norm_num⟩
  | 8 => ⟨((-1612528761/2251799813685248), (140183457/1125899906842624)), (39/562949953421312), by norm_num⟩
  | 9 => ⟨((993528679/18014398509481984), (-172742699/18014398509481984)), (49/9007199254740992), by norm_num⟩
  | 10 => ⟨((-275464641/72057594037927936), (23947223/36028797018963968)), (111/288230376151711744), by norm_num⟩
  | 11 => ⟨((1110909319/4611686018427387904), (-193151419/4611686018427387904)), (57/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-128337277/9223372036854775808), (178509815/73786976294838206464)), (27/18446744073709551616), by norm_num⟩
  | 13 => ⟨((875880583/1180591620717411303424), (-152287477/1180591620717411303424)), (187/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-1387689501/37778931862957161709568), (241274595/37778931862957161709568)), (75/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((64124871/37778931862957161709568), (-178388059/604462909807314587353088)), (7/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-1422335153/19342813113834066795298816), (30912295/2417851639229258349412352)), (157/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (1934017283867/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27828706362343/9903520314283042199192993792), (286798407415/39614081257132168796771975168)), (23163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892292908715785/39614081257132168796771975168), (5162060478833/39614081257132168796771975168)), (52131/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473056573031395/618970019642690137449562112), (1371087637239/618970019642690137449562112)), (27703/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886945634646579/77371252455336267181195264), (5483969209049/154742504910672534362390528)), (55425/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552083869276117/9671406556917033397649408), (5140815696339/9671406556917033397649408)), (51981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630500735328981/302231454903657293676544), (1124452000247/151115727451828646838272)), (45503/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891385290621845/75557863725914323419136), (7308176622557/75557863725914323419136)), (18495/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((325058042774343/1180591620717411303424), (1370116407861/1180591620717411303424)), (27759/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625147000403287/590295810358705651712), (7534555457187/590295810358705651712)), (38195/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914046412427701/36893488147419103232), (9416565081431/73786976294838206464)), (5973/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1827844939026455/9223372036854775808), (2647848041185/2305843009213693952)), (13453/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399771037010379/288230376151711744), (10588582708723/1152921504606846976)), (53881/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199031311177457/144115188075855872), (4630921170701/72057594037927936)), (94447/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498292333792509/36028797018963968), (6943205623743/18014398509481984)), (141981/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497539824222599/9007199254740992), (4336714733549/2251799813685248)), (44505/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122201473510963/2251799813685248), (17330049057507/2251799813685248)), (89419/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120256493204663/1125899906842624), (811024354457/35184372088832)), (270303/1125899906842624), by norm_num⟩
  | 0 => ⟨((557115587100213/562949953421312), (51734769283703/1125899906842624)), (548813/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557115587100213/562949953421312), (51734769283703/1125899906842624)), (2093555454734420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1100306177909991/1125899906842624), (25599297226883/281474976710656)), (1136687/1125899906842624), by norm_num⟩
  | 2 => ⟨((532990763013931/562949953421312), (100069516722433/562949953421312)), (2428453/1125899906842624), by norm_num⟩
  | 3 => ⟨((486837672897009/562949953421312), (47371997944201/140737488355328)), (5461791/1125899906842624), by norm_num⟩
  | 4 => ⟨((714469268544949/1125899906842624), (655474913163423/1125899906842624)), (6561773/562949953421312), by norm_num⟩
  | 5 => ⟨((143563337055777/2251799813685248), (415948770322525/562949953421312)), (63872555/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1220181129814497/2251799813685248), (212150274278673/2251799813685248)), (25632963/562949953421312), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1065696157/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-844544223/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1744822053109517/4503599627370496), (-31977683674839/2251799813685248)), (3422461/281474976710656), by norm_num⟩
  | 1 => ⟨((-1828082037/4294967296), (33503605/2147483648)), (15/1073741824), by norm_num⟩
  | 2 => ⟨((2008353391/8589934592), (-2300467/268435456)), (69/8589934592), by norm_num⟩
  | 3 => ⟨((-1470934477/17179869184), (13479047/4294967296)), (53/17179869184), by norm_num⟩
  | 4 => ⟨((1615986693/68719476736), (-59232987/68719476736)), (61/68719476736), by norm_num⟩
  | 5 => ⟨((-44383571/8589934592), (26029635/137438953472)), (7/34359738368), by norm_num⟩
  | 6 => ⟨((1040220513/1099511627776), (-9532159/274877906944)), (43/1099511627776), by norm_num⟩
  | 7 => ⟨((-326514011/2199023255552), (1496021/274877906944)), (7/1099511627776), by norm_num⟩
  | 8 => ⟨((358712305/17592186044416), (-26296753/35184372088832)), (1/1099511627776), by norm_num⟩
  | 9 => ⟨((-1401193765/562949953421312), (25679943/281474976710656)), (65/562949953421312), by norm_num⟩
  | 10 => ⟨((153936869/562949953421312), (-22569841/2251799813685248)), (15/1125899906842624), by norm_num⟩
  | 11 => ⟨((-491976541/18014398509481984), (72132377/72057594037927936)), (99/72057594037927936), by norm_num⟩
  | 12 => ⟨((1441310597/576460752303423488), (-6603793/72057594037927936)), (75/576460752303423488), by norm_num⟩
  | 13 => ⟨((-1948851119/9223372036854775808), (35716963/4611686018427387904)), (13/1152921504606846976), by norm_num⟩
  | 14 => ⟨((76465421/4611686018427387904), (-44844679/73786976294838206464)), (17/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-358424965/295147905179352825856), (3284461/73786976294838206464)), (41/590295810358705651712), by norm_num⟩
  | 16 => ⟨((1575080285/18889465931478580854784), (-57733587/18889465931478580854784)), (93/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-23862527061/5070602400912917605986812821504)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780508154658279/633825300114114700748351602688), (-28292588753/316912650057057350374175801344)), (5763/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945849224045655/19807040628566084398385987584), (-63652926963/39614081257132168796771975168)), (51867/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945797779238047/1237940039285380274899124224), (-67624694747/2475880078570760549798248448)), (55109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221657690801247/19342813113834066795298816), (-67617338177/154742504910672534362390528)), (55109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551494537820911/9671406556917033397649408), (-31691719659/4835703278458516698824704)), (51665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260486857917229/604462909807314587353088), (-55452695455/604462909807314587353088)), (45207/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890551017490415/75557863725914323419136), (-90095981669/75557863725914323419136)), (73461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649804095895849/2361183241434822606848), (-67559171571/4722366482869645213696)), (55097/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203036479000773/73786976294838206464), (-5804565133/36893488147419103232)), (37879/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456757016894223/18446744073709551616), (-58030041683/36893488147419103232)), (47349/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826652864065839/9223372036854775808), (-32631170421/2305843009213693952)), (106537/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597899290628953/1152921504606846976), (-130471063183/1152921504606846976)), (106539/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299500668906253/36028797018963968), (-114101889199/144115188075855872)), (93223/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496765597167491/36028797018963968), (-171032325903/36028797018963968)), (139839/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495659754129399/9007199254740992), (-106789842787/4503599627370496)), (174805/9007199254740992), by norm_num⟩
  | 2 => ⟨((2240727744474245/4503599627370496), (-426527873235/4503599627370496)), (349631/4503599627370496), by norm_num⟩
  | 1 => ⟨((279401515632901/281474976710656), (-638215398857/2251799813685248)), (524499/2251799813685248), by norm_num⟩
  | 0 => ⟨((1109352988427295/1125899906842624), (-1270139136757/2251799813685248)), (1049215/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109352988427295/1125899906842624), (-1270139136757/2251799813685248)), (4002437600142668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2186097791002363/2251799813685248), (-2502944779579/2251799813685248)), (2068775/2251799813685248), by norm_num⟩
  | 2 => ⟨((1061155005442425/1125899906842624), (-2429914959751/1125899906842624)), (2010713/1125899906842624), by norm_num⟩
  | 3 => ⟨((2000256033853989/2251799813685248), (-572545660291/140737488355328)), (3798853/1125899906842624), by norm_num⟩
  | 4 => ⟨((888387204241961/1125899906842624), (-2034351197107/281474976710656)), (13559783/2251799813685248), by norm_num⟩
  | 5 => ⟨((87614982747137/140737488355328), (-25683157964013/2251799813685248)), (21594601/2251799813685248), by norm_num⟩
  | 6 => ⟨((1744822053109517/4503599627370496), (-31977683674839/2251799813685248)), (3422461/281474976710656), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-844544223/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1065696157/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((160297802884615/562949953421312), (-57478857531327/562949953421312)), (112595875/4503599627370496), by norm_num⟩
  | 1 => ⟨((-423850899/1073741824), (151982529/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((1175164223/4294967296), (-210692523/2147483648)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((-1086082357/8589934592), (389442475/8589934592)), (101/8589934592), by norm_num⟩
  | 4 => ⟨((1505629847/34359738368), (-539881907/34359738368)), (71/17179869184), by norm_num⟩
  | 5 => ⟨((-834898467/68719476736), (299374097/68719476736)), (81/68719476736), by norm_num⟩
  | 6 => ⟨((1543220049/549755813888), (-276680415/274877906944)), (19/68719476736), by norm_num⟩
  | 7 => ⟨((-611244929/1099511627776), (54794357/274877906944)), (123/2199023255552), by norm_num⟩
  | 8 => ⟨((423682699/4398046511104), (-303844433/8796093022208)), (87/8796093022208), by norm_num⟩
  | 9 => ⟨((-1044175887/70368744177664), (93603961/17592186044416)), (109/70368744177664), by norm_num⟩
  | 10 => ⟨((1158028115/562949953421312), (-415240459/562949953421312)), (123/562949953421312), by norm_num⟩
  | 11 => ⟨((-291885063/1125899906842624), (209325639/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | 12 => ⟨((134879539/4503599627370496), (-386915937/36028797018963968)), (59/18014398509481984), by norm_num⟩
  | 13 => ⟨((-460265217/144115188075855872), (82519905/72057594037927936)), (103/288230376151711744), by norm_num⟩
  | 14 => ⟨((729214943/2305843009213693952), (-522957161/4611686018427387904)), (165/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-539150167/18446744073709551616), (193326017/18446744073709551616)), (31/9223372036854775808), by norm_num⟩
  | 16 => ⟨((1494841673/590295810358705651712), (-268006767/295147905179352825856)), (175/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-448481248417/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780124868345299/633825300114114700748351602688), (-265762069801/316912650057057350374175801344)), (92253/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945633641704231/19807040628566084398385987584), (-597900981825/39614081257132168796771975168)), (103787/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118196092817241/154742504910672534362390528), (-635192281053/2475880078570760549798248448)), (55139/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443200874241229/38685626227668133590597632), (-635105096293/154742504910672534362390528)), (110283/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551065181913513/9671406556917033397649408), (-148829602613/2417851639229258349412352)), (51697/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260111218189939/604462909807314587353088), (-260405505183/302231454903657293676544)), (90475/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889940690468447/75557863725914323419136), (-423072154265/37778931862957161709568)), (73515/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649575261553107/2361183241434822606848), (-79307048173/590295810358705651712)), (110281/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811831330992603/295147905179352825856), (-872130853957/590295810358705651712)), (151647/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913120895821779/36893488147419103232), (-272448420671/18446744073709551616)), (94789/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912884280070977/4611686018427387904), (-612754755633/4611686018427387904)), (53325/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597015307235319/1152921504606846976), (-612437174313/576460752303423488)), (53333/288230376151711744), by norm_num⟩
  | 5 => ⟨((149653693827493/18014398509481984), (-1071050929355/144115188075855872)), (93351/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495606630258263/36028797018963968), (-802574611325/18014398509481984)), (280125/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494212305796955/9007199254740992), (-2003941406495/9007199254740992)), (350283/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118918312875221/2251799813685248), (-4000407150447/4503599627370496)), (700945/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115442440717971/1125899906842624), (-1495488871695/562949953421312)), (1052371/2251799813685248), by norm_num⟩
  | 0 => ⟨((2210089165107173/2251799813685248), (-11889493181483/2251799813685248)), (263571/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210089165107173/2251799813685248), (-11889493181483/2251799813685248)), (1005443574071788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2169088356785313/2251799813685248), (-11669261139163/1125899906842624)), (520161/281474976710656), by norm_num⟩
  | 2 => ⟨((2089173106920349/2251799813685248), (-5620317204801/281474976710656)), (8103137/2251799813685248), by norm_num⟩
  | 3 => ⟨((121087102591631/140737488355328), (-41715308741999/1125899906842624)), (7679721/1125899906842624), by norm_num⟩
  | 4 => ⟨((1663795081290109/2251799813685248), (-17945417131969/281474976710656)), (13783967/1125899906842624), by norm_num⟩
  | 5 => ⟨((610090564907257/1125899906842624), (-212150274278637/2251799813685248)), (22126807/1125899906842624), by norm_num⟩
  | 6 => ⟨((160297802884615/562949953421312), (-57478857531327/562949953421312)), (112595875/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1065696157/33554432)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1237234923/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((761225298244233/4503599627370496), (413374984580867/2251799813685248)), (64767371/2251799813685248), by norm_num⟩
  | 1 => ⟨((-584194591/2147483648), (-634480831/2147483648)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((940224923/4294967296), (7977793/33554432)), (165/4294967296), by norm_num⟩
  | 3 => ⟨((-1008822425/8589934592), (-1095659735/8589934592)), (179/8589934592), by norm_num⟩
  | 4 => ⟨((811818529/17179869184), (440849079/8589934592)), (73/8589934592), by norm_num⟩
  | 5 => ⟨((-1020759/67108864), (-567615377/34359738368)), (3/1073741824), by norm_num⟩
  | 6 => ⟨((35047429/8589934592), (609027805/137438953472)), (13/17179869184), by norm_num⟩
  | 7 => ⟨((-515718043/549755813888), (-560109965/549755813888)), (97/549755813888), by norm_num⟩
  | 8 => ⟨((830016171/4398046511104), (901462213/4398046511104)), (79/2199023255552), by norm_num⟩
  | 9 => ⟨((-593715331/17592186044416), (-322410547/8796093022208)), (115/17592186044416), by norm_num⟩
  | 10 => ⟨((382219185/70368744177664), (207559903/35184372088832)), (75/70368744177664), by norm_num⟩
  | 11 => ⟨((-447387671/562949953421312), (-971795715/1125899906842624)), (89/562949953421312), by norm_num⟩
  | 12 => ⟨((480028453/4503599627370496), (521348289/4503599627370496)), (193/9007199254740992), by norm_num⟩
  | 13 => ⟨((-950862759/72057594037927936), (-516355509/36028797018963968)), (193/72057594037927936), by norm_num⟩
  | 14 => ⟨((109311041/72057594037927936), (949762437/576460752303423488)), (179/576460752303423488), by norm_num⟩
  | 15 => ⟨((-46914489/288230376151711744), (-407622313/2305843009213693952)), (39/1152921504606846976), by norm_num⟩
  | 16 => ⟨((302023829/18446744073709551616), (656042805/36893488147419103232)), (127/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (1076788027157/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444956768358581/158456325028528675187087900672), (318941595587/158456325028528675187087900672)), (46163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890932260574023/39614081257132168796771975168), (717529976133/19807040628566084398385987584)), (103875/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945390758580489/1237940039285380274899124224), (1524535172473/2475880078570760549798248448)), (13797/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886223761073571/77371252455336267181195264), (762146094853/77371252455336267181195264)), (110387/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550731448204145/9671406556917033397649408), (89297862941/604462909807314587353088)), (51749/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259819193895243/604462909807314587353088), (624956007411/302231454903657293676544)), (22643/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944733068671835/37778931862957161709568), (2030623265339/75557863725914323419136)), (147201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649397298181089/2361183241434822606848), (761272137869/2361183241434822606848)), (110419/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623173243448319/590295810358705651712), (2092810939343/590295810358705651712)), (151855/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114101874356675/4611686018427387904), (1307491446851/36893488147419103232)), (23733/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825080243621575/9223372036854775808), (183777440517/576460752303423488)), (106829/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596326941854585/1152921504606846976), (2938669087987/1152921504606846976)), (213735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598313588189327/72057594037927936), (2569345516067/144115188075855872)), (187105/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494702960915393/36028797018963968), (3850041573921/36028797018963968)), (140415/18014398509481984), by norm_num⟩
  | 3 => ⟨((746541266294807/4503599627370496), (2402799936641/4503599627370496)), (351339/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235576529480191/4503599627370496), (9590371963797/4503599627370496)), (175897/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113746698177695/1125899906842624), (14333588124007/2251799813685248)), (528831/1125899906842624), by norm_num⟩
  | 0 => ⟨((2203301035279917/2251799813685248), (28459893866637/2251799813685248)), (1062233/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203301035279917/2251799813685248), (28459893866637/2251799813685248)), (4052097324851607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2155487116131851/2251799813685248), (55693861629463/2251799813685248)), (2105561/1125899906842624), by norm_num⟩
  | 2 => ⟨((1030958185840803/1125899906842624), (53311755538993/1125899906842624)), (4135161/1125899906842624), by norm_num⟩
  | 3 => ⟨((470749056479707/562949953421312), (195264926981297/2251799813685248)), (7964529/1125899906842624), by norm_num⟩
  | 4 => ⟨((1557663507119295/2251799813685248), (163284106484739/1125899906842624)), (29402919/2251799813685248), by norm_num⟩
  | 5 => ⟨((515069943072067/1125899906842624), (225900803808673/1125899906842624)), (96107/4398046511104), by norm_num⟩
  | 6 => ⟨((761225298244233/4503599627370496), (413374984580867/2251799813685248)), (64767371/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1237234923/33554432)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1377392301/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-234859998342875/1125899906842624), (777505799331/17592186044416)), (81428457/4503599627370496), by norm_num⟩
  | 1 => ⟨((802636387/2147483648), (-170056565/2147483648)), (141/4294967296), by norm_num⟩
  | 2 => ⟨((-1438131347/4294967296), (304700461/4294967296)), (1/33554432), by norm_num⟩
  | 3 => ⟨((1717856973/8589934592), (-11373957/268435456)), (155/8589934592), by norm_num⟩
  | 4 => ⟨((-1538993249/17179869184), (326070323/17179869184)), (141/17179869184), by norm_num⟩
  | 5 => ⟨((1103002291/34359738368), (-58423959/8589934592)), (103/34359738368), by norm_num⟩
  | 6 => ⟨((-41173225/4294967296), (279151151/137438953472)), (125/137438953472), by norm_num⟩
  | 7 => ⟨((674491573/274877906944), (-142906205/274877906944)), (65/274877906944), by norm_num⟩
  | 8 => ⟨((-1208526663/2199023255552), (128026773/1099511627776)), (59/1099511627776), by norm_num⟩
  | 9 => ⟨((60149697/549755813888), (-203905051/8796093022208)), (3/274877906944), by norm_num⟩
  | 10 => ⟨((-689752251/35184372088832), (292279045/70368744177664)), (35/17592186044416), by norm_num⟩
  | 11 => ⟨((449407319/140737488355328), (-95217045/140737488355328)), (93/281474976710656), by norm_num⟩
  | 12 => ⟨((-1073639759/2251799813685248), (227474723/2251799813685248)), (113/2251799813685248), by norm_num⟩
  | 13 => ⟨((295954493/4503599627370496), (-250818455/18014398509481984)), (63/9007199254740992), by norm_num⟩
  | 14 => ⟨((-303016723/36028797018963968), (32100453/18014398509481984)), (131/144115188075855872), by norm_num⟩
  | 15 => ⟨((1158257243/1152921504606846976), (-30675355/144115188075855872)), (127/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-129707399/1152921504606846976), (219851431/9223372036854775808)), (115/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (3820309533023/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889787170937459/316912650057057350374175801344), (2262543279505/316912650057057350374175801344)), (46323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945323694731597/19807040628566084398385987584), (2544998228245/19807040628566084398385987584)), (1629/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((236309767892909/309485009821345068724781056), (5407264900141/2475880078570760549798248448)), (27701/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110758960172107/9671406556917033397649408), (5406301354043/154742504910672534362390528)), (55421/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24225710386333/151115727451828646838272), (1266845926655/2417851639229258349412352)), (51977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259568124769375/604462909807314587353088), (4432936879655/604462909807314587353088)), (11375/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472264147009333/18889465931478580854784), (1800400644387/18889465931478580854784)), (36987/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298486068641767/4722366482869645213696), (5399521955717/4722366482869645213696)), (55513/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405686700089559/147573952589676412928), (3710806263095/295147905179352825856)), (38191/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825093612876177/73786976294838206464), (4636460033175/36893488147419103232)), (47779/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228059031984457/1152921504606846976), (10426403076815/9223372036854775808)), (107611/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595713257245951/1152921504606846976), (325605070231/36028797018963968)), (107747/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598041902117923/72057594037927936), (9109019901143/144115188075855872)), (2951/4503599627370496), by norm_num⟩
  | 4 => ⟨((23341798962783/562949953421312), (13647682926353/36028797018963968)), (35489/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492025463595155/9007199254740992), (17031865348919/9007199254740992)), (177983/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116697890389227/2251799813685248), (4247561437969/562949953421312)), (22349/281474976710656), by norm_num⟩
  | 1 => ⟨((1112028299678957/1125899906842624), (6345319567947/281474976710656)), (270213/1125899906842624), by norm_num⟩
  | 0 => ⟨((548942463957091/562949953421312), (50345955748735/1125899906842624)), (137139/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((548942463957091/562949953421312), (50345955748735/1125899906842624)), (523143769384288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((534157873346819/562949953421312), (24546616294239/281474976710656)), (1118873/1125899906842624), by norm_num⟩
  | 2 => ⟨((1005114172060963/1125899906842624), (93164717594555/562949953421312)), (2318445/1125899906842624), by norm_num⟩
  | 3 => ⟨((433224940570255/562949953421312), (166340146972645/562949953421312)), (2453413/562949953421312), by norm_num⟩
  | 4 => ⟨((1136973570490481/2251799813685248), (256018141039759/562949953421312)), (20903895/2251799813685248), by norm_num⟩
  | 5 => ⟨((27087696900031/562949953421312), (1034144716272715/2251799813685248)), (40122823/2251799813685248), by norm_num⟩
  | 6 => ⟨((-234859998342875/1125899906842624), (777505799331/17592186044416)), (81428457/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1377392301/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1495893675/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((347229725513637/2251799813685248), (-473891439325521/4503599627370496)), (84426769/4503599627370496), by norm_num⟩
  | 1 => ⟨((-644376609/2147483648), (219857731/1073741824)), (5/134217728), by norm_num⟩
  | 2 => ⟨((1253898983/4294967296), (-213911695/1073741824)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-813324919/4294967296), (277501959/2147483648)), (13/536870912), by norm_num⟩
  | 4 => ⟨((791328607/8589934592), (-269996939/4294967296)), (103/8589934592), by norm_num⟩
  | 5 => ⟨((-615941747/17179869184), (420311827/17179869184)), (81/17179869184), by norm_num⟩
  | 6 => ⟨((799044865/68719476736), (-545259367/68719476736)), (107/68719476736), by norm_num⟩
  | 7 => ⟨((-27765527/8589934592), (606300421/274877906944)), (121/274877906944), by norm_num⟩
  | 8 => ⟨((864467533/1099511627776), (-589903071/1099511627776)), (15/137438953472), by norm_num⟩
  | 9 => ⟨((-747633843/4398046511104), (510177055/4398046511104)), (53/2199023255552), by norm_num⟩
  | 10 => ⟨((581931313/17592186044416), (-794206967/35184372088832)), (167/35184372088832), by norm_num⟩
  | 11 => ⟨((-411776745/70368744177664), (561983781/140737488355328)), (15/17592186044416), by norm_num⟩
  | 12 => ⟨((1068374063/1125899906842624), (-729046629/1125899906842624)), (157/1125899906842624), by norm_num⟩
  | 13 => ⟨((-639679979/4503599627370496), (218255267/2251799813685248)), (95/4503599627370496), by norm_num⟩
  | 14 => ⟨((711291293/36028797018963968), (-242688651/18014398509481984)), (107/36028797018963968), by norm_num⟩
  | 15 => ⟨((-369095719/144115188075855872), (503733663/288230376151711744)), (7/18014398509481984), by norm_num⟩
  | 16 => ⟨((359113553/1152921504606846976), (-30631889/144115188075855872)), (111/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-97501851385/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779379711056763/633825300114114700748351602688), (-461855341045/316912650057057350374175801344)), (92291/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945214535314893/19807040628566084398385987584), (-129877591273/4951760157141521099596496896)), (51917/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118140437003263/154742504910672534362390528), (-1103770495893/2475880078570760549798248448)), (55165/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110744570342793/9671406556917033397649408), (-1103557895511/154742504910672534362390528)), (110337/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387557646942957/2417851639229258349412352), (-1034359694683/9671406556917033397649408)), (51725/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259381077415789/604462909807314587353088), (-904838962981/604462909807314587353088)), (45263/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888754453727567/75557863725914323419136), (-1469940129099/75557863725914323419136)), (9195/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298261057270475/4722366482869645213696), (-1102084942007/4722366482869645213696)), (55177/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622439990421473/590295810358705651712), (-1514765542409/590295810358705651712)), (75879/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824713967981711/73786976294838206464), (-1892555483815/73786976294838206464)), (189729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824050467497377/9223372036854775808), (-1063943070077/4611686018427387904)), (106745/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797649050224685/576460752303423488), (-265792340691/144115188075855872)), (106773/576460752303423488), by norm_num⟩
  | 5 => ⟨((597863995389065/72057594037927936), (-116175437429/9007199254740992)), (186915/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493356281449979/36028797018963968), (-2784735361889/36028797018963968)), (280499/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491402851173703/9007199254740992), (-3474845884933/9007199254740992)), (87711/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232228149536949/4503599627370496), (-3465752229671/2251799813685248)), (351175/2251799813685248), by norm_num⟩
  | 1 => ⟨((555624552692207/562949953421312), (-10351902463931/2251799813685248)), (527593/1125899906842624), by norm_num⟩
  | 0 => ⟨((548354941241613/562949953421312), (-20523070777939/2251799813685248)), (2117049/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548354941241613/562949953421312), (-20523070777939/2251799813685248)), (8075901040084075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2136366225662969/2251799813685248), (-39981981354253/2251799813685248)), (1040729/562949953421312), by norm_num⟩
  | 2 => ⟨((2026140185105353/2251799813685248), (-75864785209767/2251799813685248)), (8046857/2251799813685248), by norm_num⟩
  | 3 => ⟨((910269323043129/1125899906842624), (-136524294045777/2251799813685248)), (15023125/2251799813685248), by norm_num⟩
  | 4 => ⟨((11434332921573/17592186044416), (-220754750870339/2251799813685248)), (13056757/1125899906842624), by norm_num⟩
  | 5 => ⟨((464822965447993/1125899906842624), (-143483209482745/1125899906842624)), (19532945/1125899906842624), by norm_num⟩
  | 6 => ⟨((347229725513637/2251799813685248), (-473891439325521/4503599627370496)), (84426769/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1495893675/33554432)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1598544235/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-325780647599801/2251799813685248), (739972260805649/9007199254740992)), (67109853/2251799813685248), by norm_num⟩
  | 1 => ⟨((646058857/2147483648), (-91715399/536870912)), (269/4294967296), by norm_num⟩
  | 2 => ⟨((-671720813/2147483648), (762867243/4294967296)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((931202775/4294967296), (-528779279/4294967296)), (199/4294967296), by norm_num⟩
  | 4 => ⟨((-968190867/8589934592), (34361425/536870912)), (209/8589934592), by norm_num⟩
  | 5 => ⟨((201329631/4294967296), (-457296477/17179869184)), (11/1073741824), by norm_num⟩
  | 6 => ⟨((-1116408529/68719476736), (633947527/68719476736)), (247/68719476736), by norm_num⟩
  | 7 => ⟨((1326575013/274877906944), (-753289613/274877906944)), (37/34359738368), by norm_num⟩
  | 8 => ⟨((-344816899/274877906944), (391605429/549755813888)), (39/137438953472), by norm_num⟩
  | 9 => ⟨((1274713927/4398046511104), (-723840531/4398046511104)), (291/4398046511104), by norm_num⟩
  | 10 => ⟨((-1060277237/17592186044416), (150518407/4398046511104)), (245/17592186044416), by norm_num⟩
  | 11 => ⟨((400869915/35184372088832), (-113816083/17592186044416)), (187/70368744177664), by norm_num⟩
  | 12 => ⟨((-1111447405/562949953421312), (78891297/70368744177664)), (131/281474976710656), by norm_num⟩
  | 13 => ⟨((177783839/562949953421312), (-403814991/2251799813685248)), (85/1125899906842624), by norm_num⟩
  | 14 => ⟨((-845008229/18014398509481984), (29989631/1125899906842624)), (51/4503599627370496), by norm_num⟩
  | 15 => ⟨((468572057/72057594037927936), (-532153041/144115188075855872)), (229/144115188075855872), by norm_num⟩
  | 16 => ⟨((-974368201/1152921504606846976), (276645285/576460752303423488)), (15/72057594037927936), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (427444167341/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779193757226735/633825300114114700748351602688), (4048741012377/633825300114114700748351602688)), (92599/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472554856873225/9903520314283042199192993792), (4554093974353/39614081257132168796771975168)), (104199/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890023672411375/2475880078570760549798248448), (2418918510617/1237940039285380274899124224)), (110741/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885844580364961/77371252455336267181195264), (1209209551899/38685626227668133590597632)), (110775/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550019935773065/9671406556917033397649408), (2266737332937/4835703278458516698824704)), (103887/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629598036158469/302231454903657293676544), (3965729275107/604462909807314587353088)), (11367/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888452537754363/75557863725914323419136), (100661262405/1180591620717411303424)), (147837/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298033498875883/4722366482869645213696), (4830000182147/4722366482869645213696)), (13867/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811062638543007/295147905179352825856), (3319211232021/295147905179352825856)), (19079/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912158924284721/36893488147419103232), (2073446768973/18446744073709551616)), (190931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823601087500113/9223372036854775808), (4662340089921/4611686018427387904)), (214993/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797422022928021/576460752303423488), (4658696991967/576460752303423488)), (215237/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195325444360957/144115188075855872), (8144525048125/144115188075855872)), (2947/2251799813685248), by norm_num⟩
  | 4 => ⟨((1492741990184619/36028797018963968), (6100201962401/18014398509481984)), (283461/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490616719380905/9007199254740992), (15221846471459/9007199254740992)), (177645/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115300656553549/2251799813685248), (948680304097/140737488355328)), (356739/2251799813685248), by norm_num⟩
  | 1 => ⟨((554980582119341/562949953421312), (22661015113193/1125899906842624)), (33671/70368744177664), by norm_num⟩
  | 0 => ⟨((546932576048345/562949953421312), (11223334448305/281474976710656)), (1092033/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546932576048345/562949953421312), (11223334448305/281474976710656)), (4165775303367232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((33154744482991/35184372088832), (5452000825613/70368744177664)), (1104505/562949953421312), by norm_num⟩
  | 2 => ⟨((992991775530573/1125899906842624), (164399984254719/1125899906842624)), (4505463/1125899906842624), by norm_num⟩
  | 3 => ⟨((851767822006273/1125899906842624), (289986403356387/1125899906842624)), (4631483/562949953421312), by norm_num⟩
  | 4 => ⟨((1139384246460183/2251799813685248), (219381035292001/562949953421312)), (37573609/2251799813685248), by norm_num⟩
  | 5 => ⟨((234544758170417/2251799813685248), (1776067617128031/4503599627370496)), (134616813/4503599627370496), by norm_num⟩
  | 6 => ⟨((-325780647599801/2251799813685248), (739972260805649/9007199254740992)), (67109853/2251799813685248), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1598544235/33554432)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile024Terms0

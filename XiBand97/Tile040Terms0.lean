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
namespace Reinmann.XiBand97.Tile040Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6939/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6939/256))
  have he : value ((69/80), (6939/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1260846655/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((618073625155751/1125899906842624), (9511263043155/281474976710656)), (9892519/562949953421312), by norm_num⟩
  | 1 => ⟨((-408569327/1073741824), (-100596697/4294967296)), (55/4294967296), by norm_num⟩
  | 2 => ⟨((283198677/2147483648), (69728317/8589934592)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((-1046924611/34359738368), (-8055331/4294967296)), (39/34359738368), by norm_num⟩
  | 4 => ⟨((1451345685/274877906944), (2791765/8589934592)), (7/34359738368), by norm_num⟩
  | 5 => ⟨((-1609593871/2199023255552), (-99077327/2199023255552)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((1487580605/17592186044416), (91566893/17592186044416)), (61/17592186044416), by norm_num⟩
  | 7 => ⟨((-294603515/35184372088832), (-72536381/140737488355328)), (25/70368744177664), by norm_num⟩
  | 8 => ⟨((1633628767/2251799813685248), (12569597/281474976710656)), (71/2251799813685248), by norm_num⟩
  | 9 => ⟨((-2013058087/36028797018963968), (-123912259/36028797018963968)), (45/18014398509481984), by norm_num⟩
  | 10 => ⟨((558138215/144115188075855872), (34355773/144115188075855872)), (13/72057594037927936), by norm_num⟩
  | 11 => ⟨((-1125445615/4611686018427387904), (-17318987/1152921504606846976)), (27/2305843009213693952), by norm_num⟩
  | 12 => ⟨((1040132607/73786976294838206464), (64024571/73786976294838206464)), (13/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-887341519/1180591620717411303424), (-3413727/73786976294838206464)), (91/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((1405847479/37778931862957161709568), (1352123/590295810358705651712)), (37/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-259855791/151115727451828646838272), (-31990451/302231454903657293676544)), (7/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((1440946471/19342813113834066795298816), (22174091/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (80080232651/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445262104774919/158456325028528675187087900672), (1484402659/9903520314283042199192993792)), (46105/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473076550805279/9903520314283042199192993792), (106871228915/39614081257132168796771975168)), (51869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892241247145343/2475880078570760549798248448), (56771875477/1237940039285380274899124224)), (55111/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773907157535517/154742504910672534362390528), (28383988915/38685626227668133590597632)), (55111/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776049877934137/4835703278458516698824704), (6651979793/604462909807314587353088)), (51667/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630508181292057/302231454903657293676544), (5819964763/37778931862957161709568)), (45209/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891411347983143/75557863725914323419136), (18912944871/9444732965739290427392)), (73465/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650126669705867/2361183241434822606848), (56732043385/2361183241434822606848)), (13775/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625178747111233/590295810358705651712), (155991051203/590295810358705651712)), (18941/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914068233603557/36893488147419103232), (24369464721/9223372036854775808)), (94705/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827899477898259/9223372036854775808), (219279684787/9223372036854775808)), (53273/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599145484912359/1152921504606846976), (13701426693/72057594037927936)), (26637/288230376151711744), by norm_num⟩
  | 5 => ⟨((599546311911705/72057594037927936), (191756028627/144115188075855872)), (93233/144115188075855872), by norm_num⟩
  | 4 => ⟨((23412493380443/562949953421312), (287506202361/36028797018963968)), (8741/2251799813685248), by norm_num⟩
  | 3 => ⟨((748850289368029/4503599627370496), (89789785857/2251799813685248)), (174831/9007199254740992), by norm_num⟩
  | 2 => ⟨((280600556239473/562949953421312), (358823952009/2251799813685248)), (683/8796093022208), by norm_num⟩
  | 1 => ⟨((2241314838960257/2251799813685248), (1074797457957/2251799813685248)), (524629/2251799813685248), by norm_num⟩
  | 0 => ⟨((1115431059232551/1125899906842624), (535726667383/562949953421312)), (1025/2199023255552), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115431059232551/1125899906842624), (535726667383/562949953421312)), (3910064705654233/8388608000000000000000000), by norm_num⟩
  | 1 => ⟨((2210117066938015/2251799813685248), (4245962970075/2251799813685248)), (130105/140737488355328), by norm_num⟩
  | 2 => ⟨((2169197897469899/2251799813685248), (8334733104353/2251799813685248)), (63971/35184372088832), by norm_num⟩
  | 3 => ⟨((2089595186044195/2251799813685248), (4014496629775/562949953421312)), (7918229/2251799813685248), by norm_num⟩
  | 4 => ⟨((1938960184681105/2251799813685248), (29802552717117/2251799813685248)), (14808639/2251799813685248), by norm_num⟩
  | 5 => ⟨((1669188523236777/2251799813685248), (25662122702541/1125899906842624)), (25894573/2251799813685248), by norm_num⟩
  | 6 => ⟨((618073625155751/1125899906842624), (9511263043155/281474976710656)), (9892519/562949953421312), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1260846655/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1998394667/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-7276389423479/281474976710656), (871053980849001/2251799813685248)), (52725461/1125899906842624), by norm_num⟩
  | 1 => ⟨((15247213/536870912), (-1825238433/4294967296)), (7/134217728), by norm_num⟩
  | 2 => ⟨((-134006205/8589934592), (2005229373/8589934592)), (249/8589934592), by norm_num⟩
  | 3 => ⟨((49073621/8589934592), (-1468646421/17179869184)), (185/17179869184), by norm_num⟩
  | 4 => ⟨((-53912883/34359738368), (806736503/34359738368)), (103/34359738368), by norm_num⟩
  | 5 => ⟨((94766969/274877906944), (-709032509/137438953472)), (183/274877906944), by norm_num⟩
  | 6 => ⟨((-8676013/137438953472), (1038602437/1099511627776)), (17/137438953472), by norm_num⟩
  | 7 => ⟨((2723307/274877906944), (-652012229/4398046511104)), (173/8796093022208), by norm_num⟩
  | 8 => ⟨((-95739473/70368744177664), (1432617295/70368744177664)), (3/1099511627776), by norm_num⟩
  | 9 => ⟨((93493833/562949953421312), (-87438387/35184372088832)), (95/281474976710656), by norm_num⟩
  | 10 => ⟨((-82170779/4503599627370496), (1229579347/4503599627370496)), (169/4503599627370496), by norm_num⟩
  | 11 => ⟨((65653693/36028797018963968), (-1964845063/72057594037927936)), (273/72057594037927936), by norm_num⟩
  | 12 => ⟨((-96170605/576460752303423488), (1439068621/576460752303423488)), (101/288230376151711744), by norm_num⟩
  | 13 => ⟨((130035949/9223372036854775808), (-1945819657/9223372036854775808)), (69/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-81633767/73786976294838206464), (610771825/36893488147419103232)), (175/73786976294838206464), by norm_num⟩
  | 15 => ⟨((1494731/18446744073709551616), (-1431469723/1180591620717411303424)), (207/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-52548155/9444732965739290427392), (1572630229/18889465931478580854784)), (229/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (2133059760561/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((890252372645963/316912650057057350374175801344), (2529060834055/633825300114114700748351602688)), (69337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891694408933283/39614081257132168796771975168), (355618341989/4951760157141521099596496896)), (1219/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((945795507503027/1237940039285380274899124224), (3022462935125/2475880078570760549798248448)), (82905/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886628349837195/77371252455336267181195264), (3022133329447/154742504910672534362390528)), (82921/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551489711874269/9671406556917033397649408), (2832899790887/9671406556917033397649408)), (77755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260482334430421/604462909807314587353088), (2478437112185/604462909807314587353088)), (17013/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((118158943941541/4722366482869645213696), (251675229663/4722366482869645213696)), (110615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299601762891969/4722366482869645213696), (3019528203785/4722366482869645213696)), (82989/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624282191405797/590295810358705651712), (4150917635729/590295810358705651712)), (57077/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827014816218087/73786976294838206464), (5187246583075/73786976294838206464)), (142759/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913318153283069/4611686018427387904), (5833726780023/9223372036854775808)), (80347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798940336325277/576460752303423488), (5831319761447/1152921504606846976)), (20101/144115188075855872), by norm_num⟩
  | 5 => ⟨((1197984069154431/144115188075855872), (5099696915585/144115188075855872)), (140835/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496733061727929/36028797018963968), (7644129676097/36028797018963968)), (211509/36028797018963968), by norm_num⟩
  | 3 => ⟨((747805501358183/4503599627370496), (9545684756281/9007199254740992)), (66209/2251799813685248), by norm_num⟩
  | 2 => ⟨((560151511739117/1125899906842624), (2382867258775/562949953421312)), (132755/1125899906842624), by norm_num⟩
  | 1 => ⟨((558742318170643/562949953421312), (14261665363565/1125899906842624)), (399953/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108990065128677/1125899906842624), (14190592762639/562949953421312)), (806671/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108990065128677/1125899906842624), (14190592762639/562949953421312)), (3077205662253951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1091618771253777/1125899906842624), (55909859469429/1125899906842624)), (407445/281474976710656), by norm_num⟩
  | 2 => ⟨((131950631462065/140737488355328), (108415058432935/1125899906842624)), (1661089/562949953421312), by norm_num⟩
  | 3 => ⟨((61203719885061/70368744177664), (101646232197243/562949953421312)), (3434659/562949953421312), by norm_num⟩
  | 4 => ⟨((815011505243465/1125899906842624), (176815078781713/562949953421312)), (7214963/562949953421312), by norm_num⟩
  | 5 => ⟨((478896447245423/1125899906842624), (63996063340899/140737488355328)), (59910879/2251799813685248), by norm_num⟩
  | 6 => ⟨((-7276389423479/281474976710656), (871053980849001/2251799813685248)), (52725461/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1998394667/67108864)), (3/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1260846655/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1352047647594439/4503599627370496), (83540794959361/2251799813685248)), (93107557/4503599627370496), by norm_num⟩
  | 1 => ⟨((-446876533/1073741824), (-110447057/2147483648)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((309751209/1073741824), (38278033/1073741824)), (89/4294967296), by norm_num⟩
  | 3 => ⟨((-286270903/2147483648), (-141505657/8589934592)), (21/2147483648), by norm_num⟩
  | 4 => ⟨((793711477/17179869184), (98084247/17179869184)), (119/34359738368), by norm_num⟩
  | 5 => ⟨((-220063549/17179869184), (-108778911/68719476736)), (67/68719476736), by norm_num⟩
  | 6 => ⟨((813527619/274877906944), (201066121/549755813888)), (63/274877906944), by norm_num⟩
  | 7 => ⟨((-644450715/1099511627776), (-39819547/549755813888)), (51/1099511627776), by norm_num⟩
  | 8 => ⟨((1786796785/17592186044416), (110403227/8796093022208)), (9/1099511627776), by norm_num⟩
  | 9 => ⟨((-1100900581/70368744177664), (-136045663/70368744177664)), (45/35184372088832), by norm_num⟩
  | 10 => ⟨((610468907/281474976710656), (37719867/140737488355328)), (51/281474976710656), by norm_num⟩
  | 11 => ⟨((-153870837/562949953421312), (-38029701/1125899906842624)), (13/562949953421312), by norm_num⟩
  | 12 => ⟨((1137654793/36028797018963968), (140587627/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | 13 => ⟨((-970538107/288230376151711744), (-59967949/144115188075855872)), (85/288230376151711744), by norm_num⟩
  | 14 => ⟨((1537658863/4611686018427387904), (95009405/2305843009213693952)), (137/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-1136878833/36893488147419103232), (-17561467/4611686018427387904)), (103/36893488147419103232), by norm_num⟩
  | 16 => ⟨((394012179/147573952589676412928), (194762901/590295810358705651712)), (145/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (80080232651/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27814453123515/9903520314283042199192993792), (189816528157/633825300114114700748351602688)), (92219/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891267439174711/39614081257132168796771975168), (213520870441/39614081257132168796771975168)), (25937/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945568830142571/1237940039285380274899124224), (113419122905/1237940039285380274899124224)), (110233/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886401841545355/77371252455336267181195264), (226807112945/154742504910672534362390528)), (110235/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551065368000985/9671406556917033397649408), (53149648937/2417851639229258349412352)), (103347/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315027848151559/151115727451828646838272), (185990705427/604462909807314587353088)), (45215/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889940995615575/75557863725914323419136), (302172912261/75557863725914323419136)), (18369/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324787692740493/1180591620717411303424), (226575462555/4722366482869645213696)), (110217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623663033635395/590295810358705651712), (77863294465/147573952589676412928)), (37/144115188075855872), by norm_num⟩
  | 8 => ⟨((1826242302445803/73786976294838206464), (194592197425/36893488147419103232)), (189447/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825769198319765/9223372036854775808), (437650914435/9223372036854775808)), (213137/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798508012369369/576460752303423488), (54678014663/144115188075855872)), (53287/288230376151711744), by norm_num⟩
  | 5 => ⟨((598615133782731/72057594037927936), (382491114017/144115188075855872)), (93259/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495607883658669/36028797018963968), (143306772221/9007199254740992)), (279803/36028797018963968), by norm_num⟩
  | 3 => ⟨((747107091695811/4503599627370496), (715642980611/9007199254740992)), (349799/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237841310977827/4503599627370496), (89288554319/281474976710656)), (699735/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230894225658851/2251799813685248), (267033122461/281474976710656)), (524975/1125899906842624), by norm_num⟩
  | 0 => ⟨((1105058533469007/1125899906842624), (1061490742519/562949953421312)), (1050653/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1105058533469007/1125899906842624), (1061490742519/562949953421312)), (4007923130515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2169197897469897/2251799813685248), (8334733104355/2251799813685248)), (516593/281474976710656), by norm_num⟩
  | 2 => ⟨((2089595186044191/2251799813685248), (250906039361/35184372088832)), (7992883/2251799813685248), by norm_num⟩
  | 3 => ⟨((969480092340549/1125899906842624), (7450638179281/562949953421312)), (14948257/2251799813685248), by norm_num⟩
  | 4 => ⟨((1669188523236765/2251799813685248), (25662122702547/1125899906842624)), (3267339/281474976710656), by norm_num⟩
  | 5 => ⟨((1236147250311483/2251799813685248), (76090104345257/2251799813685248)), (19971575/1125899906842624), by norm_num⟩
  | 6 => ⟨((1352047647594439/4503599627370496), (83540794959361/2251799813685248)), (93107557/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1260846655/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-365949409/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1052679650062693/4503599627370496), (393503520365235/4503599627370496)), (23541261/1125899906842624), by norm_num⟩
  | 1 => ⟨((-807868261/2147483648), (-301990263/2147483648)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((81263363/268435456), (486034579/4294967296)), (121/4294967296), by norm_num⟩
  | 3 => ⟨((-697537799/4294967296), (-260747493/4294967296)), (33/2147483648), by norm_num⟩
  | 4 => ⟨((1122643779/17179869184), (419656901/17179869184)), (27/4294967296), by norm_num⟩
  | 5 => ⟨((-90341273/4294967296), (-540329381/68719476736)), (141/68719476736), by norm_num⟩
  | 6 => ⟨((1550919145/274877906944), (579751061/274877906944)), (153/274877906944), by norm_num⟩
  | 7 => ⟨((-1426347469/1099511627776), (-133296191/274877906944)), (143/1099511627776), by norm_num⟩
  | 8 => ⟨((1147808847/4398046511104), (429063887/4398046511104)), (117/4398046511104), by norm_num⟩
  | 9 => ⟨((-51314641/1099511627776), (-306911861/17592186044416)), (43/8796093022208), by norm_num⟩
  | 10 => ⟨((1057122927/140737488355328), (98791117/35184372088832)), (7/8796093022208), by norm_num⟩
  | 11 => ⟨((-1237362703/1125899906842624), (-14454379/35184372088832)), (133/1125899906842624), by norm_num⟩
  | 12 => ⟨((331909741/2251799813685248), (124071603/2251799813685248)), (9/562949953421312), by norm_num⟩
  | 13 => ⟨((-1314924605/72057594037927936), (-491533641/72057594037927936)), (9/4503599627370496), by norm_num⟩
  | 14 => ⟨((302327073/144115188075855872), (452053073/576460752303423488)), (135/576460752303423488), by norm_num⟩
  | 15 => ⟨((-519015097/2305843009213693952), (-388027389/4611686018427387904)), (59/2305843009213693952), by norm_num⟩
  | 16 => ⟨((417661287/18446744073709551616), (78063249/9223372036854775808)), (97/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (465980780169/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827779898453/633825300114114700748351602688), (552088804079/633825300114114700748351602688)), (92255/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890933096627117/39614081257132168796771975168), (621023455899/39614081257132168796771975168)), (51895/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945391228774193/1237940039285380274899124224), (329871982825/1237940039285380274899124224)), (110281/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886224260548209/77371252455336267181195264), (329819425537/77371252455336267181195264)), (110285/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550732446914605/9671406556917033397649408), (309149880921/4835703278458516698824704)), (51699/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259820129932623/604462909807314587353088), (540900656671/604462909807314587353088)), (45239/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889467774901883/75557863725914323419136), (219688576755/18889465931478580854784)), (147035/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324698981600721/1180591620717411303424), (658882683131/4722366482869645213696)), (110285/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623175237677851/590295810358705651712), (905666341601/590295810358705651712)), (151653/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825632730421771/73786976294838206464), (1131637087181/73786976294838206464)), (94793/36893488147419103232), by norm_num⟩
  | 7 => ⟨((114067729218149/576460752303423488), (39764968391/288230376151711744)), (213311/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596330790924451/1152921504606846976), (79482094553/72057594037927936)), (6667/36028797018963968), by norm_num⟩
  | 5 => ⟨((1196631021972889/144115188075855872), (138986096467/18014398509481984)), (93357/72057594037927936), by norm_num⟩
  | 4 => ⟨((93419355180759/2251799813685248), (1666113572741/36028797018963968)), (140073/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493092599945925/9007199254740992), (2079636107357/9007199254740992)), (175157/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235601643318795/4503599627370496), (4150268283063/4503599627370496)), (701023/4503599627370496), by norm_num⟩
  | 1 => ⟨((1113771730345213/1125899906842624), (6202940279103/2251799813685248)), (65783/140737488355328), by norm_num⟩
  | 0 => ⟨((34428912715171/35184372088832), (6158158757121/1125899906842624)), (2109051/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((34428912715171/35184372088832), (6158158757121/1125899906842624)), (8045391091353606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((539017945196977/562949953421312), (24103736715811/2251799813685248)), (4150605/2251799813685248), by norm_num⟩
  | 2 => ⟨((2064155306141247/2251799813685248), (5769760951735/281474976710656)), (4018585/1125899906842624), by norm_num⟩
  | 3 => ⟨((1891201221768177/2251799813685248), (5288961572565/140737488355328)), (15064349/2251799813685248), by norm_num⟩
  | 4 => ⟨((792583985975999/1125899906842624), (142143940535105/2251799813685248)), (13218099/1125899906842624), by norm_num⟩
  | 5 => ⟨((553457857204523/1125899906842624), (200126157373235/2251799813685248)), (40557389/2251799813685248), by norm_num⟩
  | 6 => ⟨((1052679650062693/4503599627370496), (393503520365235/4503599627370496)), (23541261/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-365949409/8388608)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1629620661/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-245556639053385/9007199254740992), (29762905846981/140737488355328)), (39665443/2251799813685248), by norm_num⟩
  | 1 => ⟨((104899033/2147483648), (-813720221/2147483648)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-46988459/1073741824), (5695277/16777216)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((56128011/2147483648), (-1741579349/8589934592)), (153/8589934592), by norm_num⟩
  | 4 => ⟨((-100567895/8589934592), (1560245645/17179869184)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((144154783/34359738368), (-279558491/8589934592)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((-86096899/68719476736), (1335737529/137438953472)), (31/34359738368), by norm_num⟩
  | 7 => ⟨((88151391/274877906944), (-683805819/274877906944)), (129/549755813888), by norm_num⟩
  | 8 => ⟨((-78973045/1099511627776), (19143993/34359738368)), (59/1099511627776), by norm_num⟩
  | 9 => ⟨((125778401/8796093022208), (-975685141/8796093022208)), (95/8796093022208), by norm_num⟩
  | 10 => ⟨((-180291713/70368744177664), (1398554473/70368744177664)), (69/35184372088832), by norm_num⟩
  | 11 => ⟨((117468867/281474976710656), (-1822453251/562949953421312)), (91/281474976710656), by norm_num⟩
  | 12 => ⟨((-140317303/2251799813685248), (1088465957/2251799813685248)), (55/1125899906842624), by norm_num⟩
  | 13 => ⟨((154716835/18014398509481984), (-1200165653/18014398509481984)), (123/18014398509481984), by norm_num⟩
  | 14 => ⟨((-79204387/72057594037927936), (1228804671/144115188075855872)), (1/1125899906842624), by norm_num⟩
  | 15 => ⟨((4730507/36028797018963968), (-587125975/576460752303423488)), (31/288230376151711744), by norm_num⟩
  | 16 => ⟨((-135614891/9223372036854775808), (525994263/4611686018427387904)), (113/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (553284998303/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779581611507505/633825300114114700748351602688), (1310711861163/316912650057057350374175801344)), (23115/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890655989238505/39614081257132168796771975168), (184293325989/2475880078570760549798248448)), (3251/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890487815853109/2475880078570760549798248448), (3132491894137/2475880078570760549798248448)), (55277/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886076818783969/77371252455336267181195264), (3131935480025/154742504910672534362390528)), (6911/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550455736794387/9671406556917033397649408), (2935598406501/9671406556917033397649408)), (51843/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629788875958801/302231454903657293676544), (80251799815/18889465931478580854784)), (45375/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472268357428525/18889465931478580854784), (521498205533/9444732965739290427392)), (73755/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298499747036509/4722366482869645213696), (1564009990511/2361183241434822606848)), (55335/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25355739193483/9223372036854775808), (1074863203859/147573952589676412928)), (19029/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912560897932377/36893488147419103232), (5371954690247/73786976294838206464)), (95191/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912253730648195/4611686018427387904), (6040203269591/9223372036854775808)), (107153/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595752831291131/1152921504606846976), (6036147679507/1152921504606846976)), (3351/36028797018963968), by norm_num⟩
  | 5 => ⟨((1196123338222075/144115188075855872), (5277068889629/144115188075855872)), (93917/144115188075855872), by norm_num⟩
  | 4 => ⟨((746972113991037/18014398509481984), (3953244099213/18014398509481984)), (141053/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492128924969327/9007199254740992), (1233396399133/1125899906842624)), (176627/9007199254740992), by norm_num⟩
  | 2 => ⟨((69801681370287/140737488355328), (9843287487601/2251799813685248)), (177095/2251799813685248), by norm_num⟩
  | 1 => ⟨((4344864756565/4398046511104), (3676327271435/281474976710656)), (266813/1125899906842624), by norm_num⟩
  | 0 => ⟨((549325719982443/562949953421312), (911645396291/35184372088832)), (538323/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549325719982443/562949953421312), (911645396291/35184372088832)), (2053539280418014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1071306548248121/1125899906842624), (28466630720131/562949953421312)), (1078487/1125899906842624), by norm_num⟩
  | 2 => ⟨((1016481409320383/1125899906842624), (108345289707179/1125899906842624)), (2161457/1125899906842624), by norm_num⟩
  | 3 => ⟨((113408810530593/140737488355328), (391263813436561/2251799813685248)), (2159397/562949953421312), by norm_num⟩
  | 4 => ⟨((1394205442038765/2251799813685248), (157643724511673/562949953421312)), (4230579/562949953421312), by norm_num⟩
  | 5 => ⟨((171660920207807/562949953421312), (195210726354697/562949953421312)), (15216261/1125899906842624), by norm_num⟩
  | 6 => ⟨((-245556639053385/9007199254740992), (29762905846981/140737488355328)), (39665443/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1629620661/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1769822031/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-331504307529381/2251799813685248), (-516978337790857/4503599627370496)), (75889867/2251799813685248), by norm_num⟩
  | 1 => ⟨((38449621/134217728), (479695031/2147483648)), (71/1073741824), by norm_num⟩
  | 2 => ⟨((-299278031/1073741824), (-933443429/4294967296)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((776490877/4294967296), (605465681/4294967296)), (91/2147483648), by norm_num⟩
  | 4 => ⟨((-755490739/8589934592), (-589090907/8589934592)), (179/8589934592), by norm_num⟩
  | 5 => ⟨((1176093677/34359738368), (229263595/8589934592)), (281/34359738368), by norm_num⟩
  | 6 => ⟨((-762857541/68719476736), (-297417571/34359738368)), (23/8589934592), by norm_num⟩
  | 7 => ⟨((424129209/137438953472), (661426137/274877906944)), (103/137438953472), by norm_num⟩
  | 8 => ⟨((-206329333/274877906944), (-160884479/274877906944)), (203/1099511627776), by norm_num⟩
  | 9 => ⟨((44610927/274877906944), (278281547/2199023255552)), (177/4398046511104), by norm_num⟩
  | 10 => ⟨((-138894169/4398046511104), (-866417419/35184372088832)), (277/35184372088832), by norm_num⟩
  | 11 => ⟨((786256213/140737488355328), (613080163/140737488355328)), (99/70368744177664), by norm_num⟩
  | 12 => ⟨((-1019989297/1125899906842624), (-194173/274877906944)), (259/1125899906842624), by norm_num⟩
  | 13 => ⟨((76338751/562949953421312), (238099353/2251799813685248)), (157/4503599627370496), by norm_num⟩
  | 14 => ⟨((-679078173/36028797018963968), (-529508511/36028797018963968)), (11/2251799813685248), by norm_num⟩
  | 15 => ⟨((352380029/144115188075855872), (549533859/288230376151711744)), (23/36028797018963968), by norm_num⟩
  | 16 => ⟨((-685699875/2305843009213693952), (-534671757/2305843009213693952)), (45/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-100924896617/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779372347640687/633825300114114700748351602688), (-3824559380963/633825300114114700748351602688)), (92577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890420362779361/39614081257132168796771975168), (-67218355159/618970019642690137449562112)), (26043/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890237197910365/2475880078570760549798248448), (-2285031686983/1237940039285380274899124224)), (110711/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771902721886981/154742504910672534362390528), (-4569180492119/154742504910672534362390528)), (110743/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775110093593175/4835703278458516698824704), (-133833397407/302231454903657293676544)), (103855/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259371330066717/604462909807314587353088), (-3746397208965/604462909807314587353088)), (90907/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888737402264793/75557863725914323419136), (-3043068514521/37778931862957161709568)), (73893/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298247208953569/4722366482869645213696), (-2281532151243/2361183241434822606848)), (55447/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622419228436915/590295810358705651712), (-6271713707223/590295810358705651712)), (19071/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824685437294413/73786976294838206464), (-3917946551963/36893488147419103232)), (47711/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824014829689809/9223372036854775808), (-2202556423403/2305843009213693952)), (53721/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595258043031935/1152921504606846976), (-8803784438963/1152921504606846976)), (215115/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597843988614913/72057594037927936), (-7696066773835/144115188075855872)), (188485/144115188075855872), by norm_num⟩
  | 4 => ⟨((186660794546821/4503599627370496), (-1441201932599/4503599627370496)), (283247/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491298160650213/9007199254740992), (-14386681320313/9007199254740992)), (354969/9007199254740992), by norm_num⟩
  | 2 => ⟨((278995889029737/562949953421312), (-3587173717511/562949953421312)), (356335/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110989099991157/1125899906842624), (-21428148670435/1125899906842624)), (67241/140737488355328), by norm_num⟩
  | 0 => ⟨((1095935014565559/1125899906842624), (-42477162029717/1125899906842624)), (136199/140737488355328), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095935014565559/1125899906842624), (-42477162029717/1125899906842624)), (519557953417730287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1065165064468155/1125899906842624), (-20673333794959/281474976710656)), (1101701/562949953421312), by norm_num⟩
  | 2 => ⟨((250408233455409/281474976710656), (-156465154962001/1125899906842624)), (4492751/1125899906842624), by norm_num⟩
  | 3 => ⟨((434668829551501/562949953421312), (-69597950605103/281474976710656)), (2310617/281474976710656), by norm_num⟩
  | 4 => ⟨((602403433695821/1125899906842624), (-53738453205027/140737488355328)), (37686665/2251799813685248), by norm_num⟩
  | 5 => ⟨((316314672845599/2251799813685248), (-460037039320731/1125899906842624)), (34554015/1125899906842624), by norm_num⟩
  | 6 => ⟨((-331504307529381/2251799813685248), (-516978337790857/4503599627370496)), (75889867/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1769822031/33554432)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-945634991/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((736573789358223/4503599627370496), (17175978376041/562949953421312)), (20492525/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1460706841/4294967296), (-272494835/4294967296)), (165/4294967296), by norm_num⟩
  | 2 => ⟨((1518727243/4294967296), (70829635/1073741824)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-1052701507/4294967296), (-196381447/4294967296)), (123/4294967296), by norm_num⟩
  | 4 => ⟨((547257811/4294967296), (204181869/8589934592)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((-910392501/17179869184), (-21229213/2147483648)), (55/8589934592), by norm_num⟩
  | 6 => ⟨((1262071991/68719476736), (117719753/34359738368)), (155/68719476736), by norm_num⟩
  | 7 => ⟨((-749829979/137438953472), (-279761537/274877906944)), (187/274877906944), by norm_num⟩
  | 8 => ⟨((194903451/137438953472), (290873881/1099511627776)), (197/1099511627776), by norm_num⟩
  | 9 => ⟨((-720516147/2199023255552), (-268824547/4398046511104)), (185/4398046511104), by norm_num⟩
  | 10 => ⟨((599308483/8796093022208), (55900493/4398046511104)), (39/4398046511104), by norm_num⟩
  | 11 => ⟨((-906346877/70368744177664), (-169078993/70368744177664)), (15/8796093022208), by norm_num⟩
  | 12 => ⟨((1256463565/562949953421312), (234393255/562949953421312)), (169/562949953421312), by norm_num⟩
  | 13 => ⟨((-1607841559/4503599627370496), (-299942813/4503599627370496)), (219/4503599627370496), by norm_num⟩
  | 14 => ⟨((955260723/18014398509481984), (89101935/9007199254740992)), (33/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1059418043/144115188075855872), (-12352151/9007199254740992)), (37/36028797018963968), by norm_num⟩
  | 16 => ⟨((17210921/18014398509481984), (205484607/1152921504606846976)), (39/288230376151711744), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (60060179341/2535301200456458802993406410752)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222400310051175/79228162514264337593543950336), (142222148463/316912650057057350374175801344)), (69171/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890229740436803/39614081257132168796771975168), (159974720009/19807040628566084398385987584)), (155637/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890035271711493/2475880078570760549798248448), (339884091149/2475880078570760549798248448)), (20671/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771701481597347/154742504910672534362390528), (84953537671/38685626227668133590597632)), (41343/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550032252828691/9671406556917033397649408), (19906342177/604462909807314587353088)), (4845/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259207615507507/604462909807314587353088), (278614521897/604462909807314587353088)), (8479/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944236365120925/37778931862957161709568), (452609393037/75557863725914323419136)), (220461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298049897684243/4722366482869645213696), (339335288887/4722366482869645213696)), (20669/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622149862024609/590295810358705651712), (455457285/576460752303423488)), (28421/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824351631298421/73786976294838206464), (582688840293/73786976294838206464)), (142113/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823643283583953/9223372036854775808), (163779384363/2305843009213693952)), (319775/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594891472024587/1152921504606846976), (327304332405/576460752303423488)), (39975/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195372815033855/144115188075855872), (572210631943/144115188075855872)), (17491/9007199254740992), by norm_num⟩
  | 4 => ⟨((1492824764097559/36028797018963968), (428586688467/18014398509481984)), (209921/18014398509481984), by norm_num⟩
  | 3 => ⟨((745370315486267/4503599627370496), (534735103747/4503599627370496)), (524907/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230910220745757/4503599627370496), (133310174857/281474976710656)), (1050129/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220537534261605/2251799813685248), (3184541803661/2251799813685248)), (1575991/2251799813685248), by norm_num⟩
  | 0 => ⟨((547390726446333/562949953421312), (6309723276087/2251799813685248)), (3155211/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547390726446333/562949953421312), (6309723276087/2251799813685248)), (12036174782759856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((532257116801303/562949953421312), (3067665239851/562949953421312)), (6153693/2251799813685248), by norm_num⟩
  | 2 => ⟨((2012883924007355/2251799813685248), (23203293947555/2251799813685248)), (11703437/2251799813685248), by norm_num⟩
  | 3 => ⟨((1799077908283145/2251799813685248), (41482850373465/2251799813685248)), (21164599/2251799813685248), by norm_num⟩
  | 4 => ⟨((359152762330045/562949953421312), (66285536774583/2251799813685248)), (1081211/70368744177664), by norm_num⟩
  | 5 => ⟨((228645717319879/562949953421312), (169156305923375/4503599627370496)), (23091905/1125899906842624), by norm_num⟩
  | 6 => ⟨((736573789358223/4503599627370496), (17175978376041/562949953421312)), (20492525/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-945634991/16777216)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile040Terms0

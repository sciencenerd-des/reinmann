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
namespace Reinmann.XiBand97.Tile030Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (31473/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (31473/1280))
  have he : value ((69/80), (31473/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-285939089/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-72232280953545/562949953421312), (301078238362127/562949953421312)), (103347079/2251799813685248), by norm_num⟩
  | 1 => ⟨((23874093/268435456), (-1592190033/4294967296)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((-66193041/2147483648), (68976377/536870912)), (49/4294967296), by norm_num⟩
  | 3 => ⟨((244701439/34359738368), (-1019963333/34359738368)), (93/34359738368), by norm_num⟩
  | 4 => ⟨((-339228225/274877906944), (1413969417/274877906944)), (131/274877906944), by norm_num⟩
  | 5 => ⟨((94054035/549755813888), (-196017783/274877906944)), (37/549755813888), by norm_num⟩
  | 6 => ⟨((-173848771/8796093022208), (1449271185/17592186044416)), (139/17592186044416), by norm_num⟩
  | 7 => ⟨((137717469/70368744177664), (-1148066555/140737488355328)), (7/8796093022208), by norm_num⟩
  | 8 => ⟨((-381833901/2251799813685248), (1591558191/2251799813685248)), (79/1125899906842624), by norm_num⟩
  | 9 => ⟨((235259637/18014398509481984), (-980608065/18014398509481984)), (99/18014398509481984), by norm_num⟩
  | 10 => ⟨((-260911287/288230376151711744), (1087529145/288230376151711744)), (7/18014398509481984), by norm_num⟩
  | 11 => ⟨((263054433/4611686018427387904), (-1096462197/4611686018427387904)), (115/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-121556959/36893488147419103232), (1013346241/73786976294838206464)), (27/18446744073709551616), by norm_num⟩
  | 13 => ⟨((103700755/590295810358705651712), (-864489957/1180591620717411303424)), (187/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-82148441/9444732965739290427392), (1369642917/37778931862957161709568)), (151/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((242948097/604462909807314587353088), (-253163767/151115727451828646838272)), (113/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-336797577/19342813113834066795298816), (1403838011/19342813113834066795298816)), (159/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (2352852837583/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781044273653957/633825300114114700748351602688), (697816355965/158456325028528675187087900672)), (46237/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946150643882501/19807040628566084398385987584), (1569998489753/19807040628566084398385987584)), (26013/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892235717715441/2475880078570760549798248448), (1668021144443/1237940039285380274899124224)), (6911/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886950641527825/77371252455336267181195264), (26061032591/1208925819614629174706176)), (55299/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776046940997649/4835703278458516698824704), (781769841529/2417851639229258349412352)), (51855/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261010856473061/604462909807314587353088), (2735949849675/604462909807314587353088)), (22693/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236425214197327/9444732965739290427392), (4445459780779/75557863725914323419136)), (36887/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650122756333677/2361183241434822606848), (3333693343269/4722366482869645213696)), (55351/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203145876138891/73786976294838206464), (2291587859813/295147905179352825856)), (76139/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828120330896585/73786976294838206464), (2863995177305/36893488147419103232)), (95223/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913939656335077/4611686018427387904), (3221321021927/4611686018427387904)), (13399/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199890350765855/144115188075855872), (402559831343/72057594037927936)), (26819/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199069953909547/144115188075855872), (5633941121095/144115188075855872)), (93961/144115188075855872), by norm_num⟩
  | 4 => ⟨((187294990495565/4503599627370496), (8447115693917/36028797018963968)), (141129/36028797018963968), by norm_num⟩
  | 3 => ⟨((187205142512705/1125899906842624), (2638061251827/2251799813685248)), (88371/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122327996585675/2251799813685248), (2635564339219/562949953421312)), (88619/1125899906842624), by norm_num⟩
  | 1 => ⟨((560254586295803/562949953421312), (15788370710943/1125899906842624)), (267097/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114987368497113/1125899906842624), (31476403936625/1125899906842624)), (134791/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114987368497113/1125899906842624), (31476403936625/1125899906842624)), (514186860204601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1103300622332291/1125899906842624), (62342651565661/1125899906842624)), (137253/140737488355328), by norm_num⟩
  | 2 => ⟨((538851477675887/562949953421312), (122182595188461/1125899906842624)), (71049/35184372088832), by norm_num⟩
  | 3 => ⟨((1018309946060967/1125899906842624), (233904529393587/1125899906842624)), (1211485/281474976710656), by norm_num⟩
  | 4 => ⟨((872407761477105/1125899906842624), (211552827442851/562949953421312)), (2694803/281474976710656), by norm_num⟩
  | 5 => ⟨((516988147482453/1125899906842624), (81961250508109/140737488355328)), (12403069/562949953421312), by norm_num⟩
  | 6 => ⟨((-72232280953545/562949953421312), (301078238362127/562949953421312)), (103347079/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-285939089/16777216)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-906405467/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-265858260525455/2251799813685248), (-1663060981224617/4503599627370496)), (74344139/2251799813685248), by norm_num⟩
  | 1 => ⟨((278544571/2147483648), (217802433/536870912)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-306012489/4294967296), (-478560859/2147483648)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((112063027/4294967296), (1402007575/17179869184)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((-246227637/34359738368), (-1540262751/68719476736)), (75/34359738368), by norm_num⟩
  | 5 => ⟨((432813933/274877906944), (1353721269/274877906944)), (67/137438953472), by norm_num⟩
  | 6 => ⟨((-158498235/549755813888), (-247869137/274877906944)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((199003553/4398046511104), (1244855223/8796093022208)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-218627749/35184372088832), (-683806623/35184372088832)), (143/70368744177664), by norm_num⟩
  | 9 => ⟨((426999345/562949953421312), (1335534861/562949953421312)), (71/281474976710656), by norm_num⟩
  | 10 => ⟨((-187642691/2251799813685248), (-146723501/562949953421312)), (127/4503599627370496), by norm_num⟩
  | 11 => ⟨((299849551/36028797018963968), (937845767/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 12 => ⟨((-439224535/576460752303423488), (-686885923/288230376151711744)), (155/576460752303423488), by norm_num⟩
  | 13 => ⟨((37118267/576460752303423488), (928764697/4611686018427387904)), (107/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-186416385/36893488147419103232), (-1166116925/73786976294838206464)), (137/73786976294838206464), by norm_num⟩
  | 15 => ⟨((54613155/147573952589676412928), (1366517743/1180591620717411303424)), (163/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-239994733/9444732965739290427392), (-750636593/9444732965739290427392)), (91/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-2449231274039/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890251829570105/316912650057057350374175801344), (-725982342741/158456325028528675187087900672)), (46243/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472923280535829/9903520314283042199192993792), (-1633317639125/19807040628566084398385987584)), (813/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((945794783778325/1237940039285380274899124224), (-3470463343877/2475880078570760549798248448)), (55295/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773255161983269/154742504910672534362390528), (-3470084587933/154742504910672534362390528)), (55307/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387872043608757/2417851639229258349412352), (-1626400927659/4835703278458516698824704)), (51863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260480893348763/604462909807314587353088), (-2845799157647/604462909807314587353088)), (45393/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890540581707033/75557863725914323419136), (-4623668965701/75557863725914323419136)), (73787/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299599714790741/4722366482869645213696), (-3467091349891/4722366482869645213696)), (55361/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406069780033053/147573952589676412928), (-4766177418987/590295810358705651712)), (76155/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827010594644141/73786976294838206464), (-5956111855653/73786976294838206464)), (95245/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456657757934917/2305843009213693952), (-6698411977659/9223372036854775808)), (26805/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597874741414787/1152921504606846976), (-6695644320073/1152921504606846976)), (107307/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197978141598951/144115188075855872), (-2927787354949/72057594037927936)), (11749/18014398509481984), by norm_num⟩
  | 4 => ⟨((374180674196809/9007199254740992), (-8777132792077/36028797018963968)), (1103/281474976710656), by norm_num⟩
  | 3 => ⟨((373898867967493/2251799813685248), (-10960512231307/9007199254740992)), (22103/1125899906842624), by norm_num⟩
  | 2 => ⟨((1120283638912467/2251799813685248), (-342004736611/70368744177664)), (44335/562949953421312), by norm_num⟩
  | 1 => ⟨((1117445954202523/1125899906842624), (-16375308318151/1125899906842624)), (33413/140737488355328), by norm_num⟩
  | 0 => ⟨((1108874453786161/1125899906842624), (-16293418812293/562949953421312)), (539789/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108874453786161/1125899906842624), (-16293418812293/562949953421312)), (2059131626609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1091163295073359/1125899906842624), (-64188142395205/1125899906842624)), (273625/281474976710656), by norm_num⟩
  | 2 => ⟨((65864936776361/70368744177664), (-124415579990593/1125899906842624)), (2246261/1125899906842624), by norm_num⟩
  | 3 => ⟨((972641857698019/1125899906842624), (-58226307758067/281474976710656)), (2350713/562949953421312), by norm_num⟩
  | 4 => ⟨((792066267422395/1125899906842624), (-100601028209551/281474976710656)), (10068019/1125899906842624), by norm_num⟩
  | 5 => ⟨((826787353175261/2251799813685248), (-1132359001769517/2251799813685248)), (5340595/281474976710656), by norm_num⟩
  | 6 => ⟨((-265858260525455/2251799813685248), (-1663060981224617/4503599627370496)), (74344139/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-906405467/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-285939089/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-607020945178447/2251799813685248), (-618103055739151/4503599627370496)), (240585515/4503599627370496), by norm_num⟩
  | 1 => ⟨((802526201/2147483648), (204294391/1073741824)), (161/2147483648), by norm_num⟩
  | 2 => ⟨((-1112537547/4294967296), (-566424325/4294967296)), (225/4294967296), by norm_num⟩
  | 3 => ⟨((1028203019/8589934592), (255609/4194304)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((-89087003/2147483648), (-362853699/17179869184)), (147/17179869184), by norm_num⟩
  | 5 => ⟨((790405183/68719476736), (402417629/68719476736)), (165/68719476736), by norm_num⟩
  | 6 => ⟨((-730489499/274877906944), (-92978215/68719476736)), (77/137438953472), by norm_num⟩
  | 7 => ⟨((144667639/274877906944), (294617543/1099511627776)), (247/2199023255552), by norm_num⟩
  | 8 => ⟨((-802207729/8796093022208), (-408426639/8796093022208)), (173/8796093022208), by norm_num⟩
  | 9 => ⟨((988529823/70368744177664), (251644243/35184372088832)), (215/70368744177664), by norm_num⟩
  | 10 => ⟨((-34259833/17592186044416), (-69770599/70368744177664)), (241/562949953421312), by norm_num⟩
  | 11 => ⟨((1105319873/4503599627370496), (562749603/4503599627370496)), (245/4503599627370496), by norm_num⟩
  | 12 => ⟨((-127691559/4503599627370496), (-130022767/9007199254740992)), (229/36028797018963968), by norm_num⟩
  | 13 => ⟨((871473665/288230376151711744), (221845943/144115188075855872)), (197/288230376151711744), by norm_num⟩
  | 14 => ⟨((-345176865/1152921504606846976), (-702957211/4611686018427387904)), (157/2305843009213693952), by norm_num⟩
  | 15 => ⟨((1020835715/36893488147419103232), (519736329/36893488147419103232)), (235/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-1415178795/590295810358705651712), (-360253771/295147905179352825856)), (41/73786976294838206464), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-3478844708719/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445028986511673/158456325028528675187087900672), (-2061501954807/316912650057057350374175801344)), (92605/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891256719433371/39614081257132168796771975168), (-4637862203007/39614081257132168796771975168)), (104207/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891125602545995/2475880078570760549798248448), (-2463562266595/1237940039285380274899124224)), (55375/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772790874094979/154742504910672534362390528), (-4926444811819/154742504910672534362390528)), (1731/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1551052561651489/9671406556917033397649408), (-4617819721777/9671406556917033397649408)), (12987/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260099389465089/604462909807314587353088), (-1009967467811/151115727451828646838272)), (90945/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944959997870653/37778931862957161709568), (-6563433864601/75557863725914323419136)), (147853/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162391714229395/590295810358705651712), (-4921389853433/4722366482869645213696)), (110949/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202954682146113/73786976294838206464), (-6764984157231/590295810358705651712)), (76325/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913103574895925/36893488147419103232), (-8453339195117/73786976294838206464)), (95479/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456431319995407/2305843009213693952), (-9506030390377/9223372036854775808)), (107513/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399241661878567/288230376151711744), (-9501058524243/1152921504606846976)), (107637/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197180928968725/144115188075855872), (-8307830652005/144115188075855872)), (47161/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495521628013815/36028797018963968), (-12450549369653/36028797018963968)), (283525/36028797018963968), by norm_num⟩
  | 3 => ⟨((373521243422645/2251799813685248), (-15543580347939/9007199254740992)), (355385/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118759447379483/2251799813685248), (-1939268295357/281474976710656)), (44607/281474976710656), by norm_num⟩
  | 1 => ⟨((34847675261309/35184372088832), (-23197549765221/1125899906842624)), (538967/1125899906842624), by norm_num⟩
  | 0 => ⟨((552049288350027/562949953421312), (-11524979316611/281474976710656)), (1092707/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552049288350027/562949953421312), (-11524979316611/281474976710656)), (4168346409324264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080831837096163/1125899906842624), (-90414525715003/1125899906842624)), (2232579/1125899906842624), by norm_num⟩
  | 2 => ⟨((1030307105072479/1125899906842624), (-173590738101703/1125899906842624)), (1161249/281474976710656), by norm_num⟩
  | 3 => ⟨((916066321828291/1125899906842624), (-158852283186093/562949953421312)), (9933567/1125899906842624), by norm_num⟩
  | 4 => ⟨((655690004064869/1125899906842624), (-516988147482459/1125899906842624)), (21770579/1125899906842624), by norm_num⟩
  | 5 => ⟨((144464561907081/1125899906842624), (-1204312953448517/2251799813685248)), (22675091/562949953421312), by norm_num⟩
  | 6 => ⟨((-607020945178447/2251799813685248), (-618103055739151/4503599627370496)), (240585515/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-285939089/8388608)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-165982501/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-167882574805497/2251799813685248), (-1072492997880443/4503599627370496)), (192519389/4503599627370496), by norm_num⟩
  | 1 => ⟨((257679539/2147483648), (205768453/536870912)), (75/1073741824), by norm_num⟩
  | 2 => ⟨((-414719219/4294967296), (-662343099/2147483648)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((111244139/2147483648), (355333365/2147483648)), (263/8589934592), by norm_num⟩
  | 4 => ⟨((-179040535/8589934592), (-1143773979/17179869184)), (107/8589934592), by norm_num⟩
  | 5 => ⟨((57630925/8589934592), (368166641/17179869184)), (139/34359738368), by norm_num⟩
  | 6 => ⟨((-494684777/274877906944), (-1580110267/274877906944)), (75/68719476736), by norm_num⟩
  | 7 => ⟨((227475553/549755813888), (726596963/549755813888)), (139/549755813888), by norm_num⟩
  | 8 => ⟨((-366107779/4398046511104), (-292353175/1099511627776)), (113/2199023255552), by norm_num⟩
  | 9 => ⟨((261878995/17592186044416), (13070119/274877906944)), (41/4398046511104), by norm_num⟩
  | 10 => ⟨((-168591193/70368744177664), (-538509953/70368744177664)), (213/140737488355328), by norm_num⟩
  | 11 => ⟨((98668021/281474976710656), (1260652123/1125899906842624)), (251/1125899906842624), by norm_num⟩
  | 12 => ⟨((-211733405/4503599627370496), (-338156887/2251799813685248)), (271/9007199254740992), by norm_num⟩
  | 13 => ⟨((26213213/4503599627370496), (669836941/36028797018963968)), (271/72057594037927936), by norm_num⟩
  | 14 => ⟨((-385723783/576460752303423488), (-616034839/288230376151711744)), (251/576460752303423488), by norm_num⟩
  | 15 => ⟨((331092523/4611686018427387904), (528783907/2305843009213693952)), (217/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-133218215/18446744073709551616), (-212761217/9223372036854775808)), (177/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-610338754357/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779823474338249/633825300114114700748351602688), (-2892490053809/633825300114114700748351602688)), (92485/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890928001284299/39614081257132168796771975168), (-3253642902091/39614081257132168796771975168)), (813/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((945388363174781/1237940039285380274899124224), (-1728252503757/1237940039285380274899124224)), (27647/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772442432993173/154742504910672534362390528), (-1727976565985/77371252455336267181195264)), (27653/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((6057524844799/37778931862957161709568), (-3239369742985/9671406556917033397649408)), (25931/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259814425249897/604462909807314587353088), (-2833862262545/604462909807314587353088)), (2837/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((944728897401173/37778931862957161709568), (-2301963526345/37778931862957161709568)), (147571/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298787820473071/4722366482869645213696), (-3451983674509/4722366482869645213696)), (865/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1623163083858545/590295810358705651712), (-4744915150311/590295810358705651712)), (152307/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825616027165069/73786976294838206464), (-5928800723941/73786976294838206464)), (190485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912531400391021/4611686018427387904), (-6666679528419/9223372036854775808)), (107217/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798153666434183/576460752303423488), (-3331326935859/576460752303423488)), (13413/72057594037927936), by norm_num⟩
  | 5 => ⟨((598303792571887/72057594037927936), (-728161822885/18014398509481984)), (187979/144115188075855872), by norm_num⟩
  | 4 => ⟨((747334358085085/18014398509481984), (-4364445021635/18014398509481984)), (35295/4503599627370496), by norm_num⟩
  | 3 => ⟨((746515622620831/4503599627370496), (-10895279239021/9007199254740992)), (88409/2251799813685248), by norm_num⟩
  | 2 => ⟨((558862147506745/1125899906842624), (-2717886020421/562949953421312)), (88667/562949953421312), by norm_num⟩
  | 1 => ⟨((556809588271773/562949953421312), (-1015501890165/70368744177664)), (66823/140737488355328), by norm_num⟩
  | 0 => ⟨((550635018970175/562949953421312), (-32259230322077/1125899906842624)), (539761/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550635018970175/562949953421312), (-32259230322077/1125899906842624)), (2059024812938499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1076254675180059/1125899906842624), (-63107072990789/1125899906842624)), (2173675/1125899906842624), by norm_num⟩
  | 2 => ⟨((256315329668737/281474976710656), (-120648881717617/1125899906842624)), (2199665/562949953421312), by norm_num⟩
  | 3 => ⟨((460344926139281/562949953421312), (-219729357493857/1125899906842624)), (8955037/1125899906842624), by norm_num⟩
  | 4 => ⟨((1419999786279037/2251799813685248), (-718723177656537/2251799813685248)), (9070519/562949953421312), by norm_num⟩
  | 5 => ⟨((166515288994229/562949953421312), (-453231567239453/1125899906842624)), (68920257/2251799813685248), by norm_num⟩
  | 6 => ⟨((-167882574805497/2251799813685248), (-1072492997880443/4503599627370496)), (192519389/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-165982501/4194304)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1478283645/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1915333909792899/9007199254740992), (-70986035587179/4503599627370496)), (63033467/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1636418185/4294967296), (60648871/2147483648)), (7/536870912), by norm_num⟩
  | 2 => ⟨((733016945/2147483648), (-108668189/4294967296)), (13/1073741824), by norm_num⟩
  | 3 => ⟨((-1751186737/8589934592), (64902419/4294967296)), (1/134217728), by norm_num⟩
  | 4 => ⟨((1568852709/17179869184), (-29072381/4294967296)), (59/17179869184), by norm_num⟩
  | 5 => ⟨((-1124402679/34359738368), (41672571/17179869184)), (11/8589934592), by norm_num⟩
  | 6 => ⟨((671553049/68719476736), (-49778149/68719476736)), (55/137438953472), by norm_num⟩
  | 7 => ⟨((-171894505/68719476736), (50965983/274877906944)), (29/274877906944), by norm_num⟩
  | 8 => ⟨((307993607/549755813888), (-91318783/2199023255552)), (27/1099511627776), by norm_num⟩
  | 9 => ⟨((-30658359/274877906944), (72720575/8796093022208)), (11/2199023255552), by norm_num⟩
  | 10 => ⟨((703134785/35184372088832), (-104238223/70368744177664)), (65/70368744177664), by norm_num⟩
  | 11 => ⟨((-1832506777/562949953421312), (135832599/562949953421312)), (87/562949953421312), by norm_num⟩
  | 12 => ⟨((1094470457/2251799813685248), (-81126449/2251799813685248)), (27/1125899906842624), by norm_num⟩
  | 13 => ⟨((-603393171/9007199254740992), (2795367/562949953421312)), (61/18014398509481984), by norm_num⟩
  | 14 => ⟨((617791673/72057594037927936), (-91586291/144115188075855872)), (1/2251799813685248), by norm_num⟩
  | 15 => ⟨((-590364843/576460752303423488), (43760161/576460752303423488)), (63/1152921504606846976), by norm_num⟩
  | 16 => ⟨((528895899/4611686018427387904), (-78407683/9223372036854775808)), (29/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-12047304557/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779585276545295/633825300114114700748351602688), (-57079244969/316912650057057350374175801344)), (46107/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945330162438679/19807040628566084398385987584), (-16051347219/4951760157141521099596496896)), (25935/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890492692449701/2475880078570760549798248448), (-68207470905/1237940039285380274899124224)), (6889/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772158817725213/154742504910672534362390528), (-34097687487/38685626227668133590597632)), (55113/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460915572093/9671406556917033397649408), (-63920315147/4835703278458516698824704)), (51669/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629791302778139/302231454903657293676544), (-27958715139/151115727451828646838272)), (45211/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236135240081471/9444732965739290427392), (-181683492383/75557863725914323419136)), (18367/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81156665198585/295147905179352825856), (-136220497275/4722366482869645213696)), (27551/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622777647790447/590295810358705651712), (-187234762673/590295810358705651712)), (37883/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825136004747345/73786976294838206464), (-233940869279/73786976294838206464)), (94709/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824525210701269/9223372036854775808), (-16440156381/576460752303423488)), (106551/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595772783295787/1152921504606846976), (-65716599521/288230376151711744)), (106555/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299035817536513/36028797018963968), (-28726267551/18014398509481984)), (93239/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493979063706295/36028797018963968), (-21519980761/2251799813685248)), (139867/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492181088367103/9007199254740992), (-214854175571/4503599627370496)), (683/35184372088832), by norm_num⟩
  | 2 => ⟨((2233783897119537/4503599627370496), (-53584154875/281474976710656)), (174869/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224829997971681/2251799813685248), (-640428311327/1125899906842624)), (524719/2251799813685248), by norm_num⟩
  | 0 => ⟨((2198075900290053/2251799813685248), (-2541135494565/2251799813685248)), (262473/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2198075900290053/2251799813685248), (-2541135494565/2251799813685248)), (1001255037547874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1072815437833957/1125899906842624), (-4961017099325/2251799813685248)), (1026029/1125899906842624), by norm_num⟩
  | 2 => ⟨((2044456711893261/2251799813685248), (-590889085607/140737488355328)), (489957/281474976710656), by norm_num⟩
  | 3 => ⟨((928082913726605/1125899906842624), (-17167382638003/2251799813685248)), (893799/281474976710656), by norm_num⟩
  | 4 => ⟨((764956289418177/1125899906842624), (-14151128713047/1125899906842624)), (11897211/2251799813685248), by norm_num⟩
  | 5 => ⟨((519546956813397/1125899906842624), (-76916214989435/4503599627370496)), (16465417/2251799813685248), by norm_num⟩
  | 6 => ⟨((1915333909792899/9007199254740992), (-70986035587179/4503599627370496)), (63033467/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1478283645/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-802732509/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-630577594997047/4503599627370496), (556074565211225/4503599627370496)), (75999633/2251799813685248), by norm_num⟩
  | 1 => ⟨((73137721/268435456), (-515971727/2147483648)), (143/2147483648), by norm_num⟩
  | 2 => ⟨((-1138555469/4294967296), (251008655/1073741824)), (35/536870912), by norm_num⟩
  | 3 => ⟨((738508881/4294967296), (-651253719/4294967296)), (183/4294967296), by norm_num⟩
  | 4 => ⟨((-718535963/8589934592), (633640611/8589934592)), (45/2147483648), by norm_num⟩
  | 5 => ⟨((559282569/17179869184), (-986406157/34359738368)), (141/17179869184), by norm_num⟩
  | 6 => ⟨((-362771209/34359738368), (639819251/68719476736)), (185/68719476736), by norm_num⟩
  | 7 => ⟨((806765917/274877906944), (-711446157/274877906944)), (207/274877906944), by norm_num⟩
  | 8 => ⟨((-784946993/1099511627776), (692205149/1099511627776)), (203/1099511627776), by norm_num⟩
  | 9 => ⟨((678860587/4398046511104), (-149663225/1099511627776)), (177/4398046511104), by norm_num⟩
  | 10 => ⟨((-1056801365/35184372088832), (931939803/35184372088832)), (277/35184372088832), by norm_num⟩
  | 11 => ⟨((373898273/70368744177664), (-164861011/35184372088832)), (197/140737488355328), by norm_num⟩
  | 12 => ⟨((-60631037/70368744177664), (855479239/1125899906842624)), (129/562949953421312), by norm_num⟩
  | 13 => ⟨((580837171/4503599627370496), (-512210995/4503599627370496)), (39/1125899906842624), by norm_num⟩
  | 14 => ⟨((-80732639/4503599627370496), (71194041/4503599627370496)), (175/36028797018963968), by norm_num⟩
  | 15 => ⟨((335143385/144115188075855872), (-591092083/288230376151711744)), (183/288230376151711744), by norm_num⟩
  | 16 => ⟨((-326079457/1152921504606846976), (287553021/1152921504606846976)), (45/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (3150882643693/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444843181040733/158456325028528675187087900672), (3731344475319/633825300114114700748351602688)), (92567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945210404024077/19807040628566084398385987584), (2098562402241/19807040628566084398385987584)), (52081/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890237698723807/2475880078570760549798248448), (4458679560407/2475880078570760549798248448)), (110699/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771903253864095/154742504910672534362390528), (2228909163867/77371252455336267181195264)), (110729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550220719009147/9671406556917033397649408), (522286212077/1208925819614629174706176)), (51921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259371828486643/604462909807314587353088), (1827544291041/302231454903657293676544)), (90895/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944369137085905/37778931862957161709568), (5937803680733/75557863725914323419136)), (36941/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649123958535349/2361183241434822606848), (4451852080731/4722366482869645213696)), (110877/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622420290074875/590295810358705651712), (764857292377/73786976294838206464)), (152543/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824686896172943/73786976294838206464), (955614512377/9223372036854775808)), (190809/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824016651977737/9223372036854775808), (4297751713467/4611686018427387904)), (26855/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398815022826179/288230376151711744), (8589220873925/1152921504606846976)), (26883/144115188075855872), by norm_num⟩
  | 5 => ⟨((298922505812959/36028797018963968), (117320349385/2251799813685248)), (188435/144115188075855872), by norm_num⟩
  | 4 => ⟨((373322482962661/9007199254740992), (11248626668633/36028797018963968)), (141579/18014398509481984), by norm_num⟩
  | 3 => ⟨((372825878435989/2251799813685248), (14036072457319/9007199254740992)), (88709/2251799813685248), by norm_num⟩
  | 2 => ⟨((557995114892839/1125899906842624), (6999514271061/1125899906842624)), (356169/2251799813685248), by norm_num⟩
  | 1 => ⟨((555501197132171/562949953421312), (10453005955435/562949953421312)), (268797/562949953421312), by norm_num⟩
  | 0 => ⟨((1095974632373591/1125899906842624), (20721188663313/562949953421312)), (1088589/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095974632373591/1125899906842624), (20721188663313/562949953421312)), (4152637485984420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065319320907983/1125899906842624), (40340881084721/562949953421312)), (1099725/562949953421312), by norm_num⟩
  | 2 => ⟨((1002216717396713/1125899906842624), (152681138992267/1125899906842624)), (1119359/281474976710656), by norm_num⟩
  | 3 => ⟨((871415667114543/1125899906842624), (135908697566497/562949953421312)), (9185509/1125899906842624), by norm_num⟩
  | 4 => ⟨((608829048150559/1125899906842624), (841516853402721/2251799813685248)), (18653839/1125899906842624), by norm_num⟩
  | 5 => ⟨((343965134120537/2251799813685248), (227524623523859/562949953421312)), (17058141/562949953421312), by norm_num⟩
  | 6 => ⟨((-630577594997047/4503599627370496), (556074565211225/4503599627370496)), (75999633/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-802732509/16777216)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-857817267/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((972698878107653/9007199254740992), (-1139975580834481/9007199254740992)), (33302081/1125899906842624), by norm_num⟩
  | 1 => ⟨((-60280277/268435456), (565174241/2147483648)), (267/4294967296), by norm_num⟩
  | 2 => ⟨((501397249/2147483648), (-293811699/1073741824)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((-695084179/4294967296), (814619003/4294967296)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((361346729/4294967296), (-423488149/4294967296)), (207/8589934592), by norm_num⟩
  | 5 => ⟨((-601119519/17179869184), (88061885/2147483648)), (175/17179869184), by norm_num⟩
  | 6 => ⟨((104166075/8589934592), (-976637557/68719476736)), (245/68719476736), by norm_num⟩
  | 7 => ⟨((-495102317/137438953472), (145061479/34359738368)), (37/34359738368), by norm_num⟩
  | 8 => ⟨((514768163/549755813888), (-603293731/549755813888)), (39/137438953472), by norm_num⟩
  | 9 => ⟨((-475746801/2199023255552), (1115123597/4398046511104)), (291/4398046511104), by norm_num⟩
  | 10 => ⟨((791430129/17592186044416), (-927533733/17592186044416)), (61/4398046511104), by norm_num⟩
  | 11 => ⟨((-299224125/35184372088832), (175341107/17592186044416)), (187/70368744177664), by norm_num⟩
  | 12 => ⟨((414812717/281474976710656), (-60768597/35184372088832)), (131/281474976710656), by norm_num⟩
  | 13 => ⟨((-66352215/281474976710656), (9720365/35184372088832)), (85/1125899906842624), by norm_num⟩
  | 14 => ⟨((315372691/9007199254740992), (-369607877/9007199254740992)), (51/4503599627370496), by norm_num⟩
  | 15 => ⟨((-699519013/144115188075855872), (819816505/144115188075855872)), (57/36028797018963968), by norm_num⟩
  | 16 => ⟨((727304447/1152921504606846976), (-852380249/1152921504606846976)), (15/72057594037927936), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-35187245973/316912650057057350374175801344)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779201573170941/633825300114114700748351602688), (-1333171036299/633825300114114700748351602688)), (138497/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890228667858171/39614081257132168796771975168), (-1499580456635/39614081257132168796771975168)), (77911/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890034065342449/2475880078570760549798248448), (-199126583727/309485009821345068724781056)), (165575/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771700200182081/154742504910672534362390528), (-796342375461/77371252455336267181195264)), (20699/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550030971809083/9671406556917033397649408), (-1492793628399/9671406556917033397649408)), (38815/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259206414971865/604462909807314587353088), (-1305846198523/604462909807314587353088)), (67935/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888470630144623/75557863725914323419136), (-2121347359111/75557863725914323419136)), (220821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298048192142531/4722366482869645213696), (-1590439605831/4722366482869645213696)), (41411/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811073652544543/295147905179352825856), (-2185927118673/590295810358705651712)), (227807/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456087029437113/18446744073709551616), (-682754645109/18446744073709551616)), (142415/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823638894998745/9223372036854775808), (-3070485338353/9223372036854775808)), (160265/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797443269735911/576460752303423488), (-383512351909/144115188075855872)), (320651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298841972058115/36028797018963968), (-1340951968497/72057594037927936)), (280705/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492816155120249/36028797018963968), (-4017496628099/36028797018963968)), (421329/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490727743318247/9007199254740992), (-1253126257685/2251799813685248)), (527139/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230878091777541/4503599627370496), (-2499241163811/1125899906842624)), (1055709/4503599627370496), by norm_num⟩
  | 1 => ⟨((277559193266927/281474976710656), (-14925514663987/2251799813685248)), (396789/562949953421312), by norm_num⟩
  | 0 => ⟨((547343071405815/562949953421312), (-3696548102013/281474976710656)), (797183/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547343071405815/562949953421312), (-3696548102013/281474976710656)), (3041011812450218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2128287092833639/2251799813685248), (-57505076022015/2251799813685248)), (3142207/1125899906842624), by norm_num⟩
  | 2 => ⟨((2010080597860215/2251799813685248), (-27175442134391/562949953421312)), (12200395/2251799813685248), by norm_num⟩
  | 3 => ⟨((223632664354039/281474976710656), (-97033188546569/1125899906842624)), (22959397/2251799813685248), by norm_num⟩
  | 4 => ⟨((1404689089273365/2251799813685248), (-308372569938869/2251799813685248)), (40440023/2251799813685248), by norm_num⟩
  | 5 => ⟨((208506300628845/562949953421312), (-192365050299655/1125899906842624)), (61529675/2251799813685248), by norm_num⟩
  | 6 => ⟨((972698878107653/9007199254740992), (-1139975580834481/9007199254740992)), (33302081/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-857817267/16777216)), (3/33554432), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile030Terms0

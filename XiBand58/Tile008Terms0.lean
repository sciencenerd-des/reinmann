/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile008Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2991/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2991/160))
  have he : value ((15/16), (2991/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-1739128909/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1086945201019267/2251799813685248), (-448255403660709/2251799813685248)), (24990331/2251799813685248), by norm_num⟩
  | 1 => ⟨((-718510629/2147483648), (592626513/4294967296)), (35/4294967296), by norm_num⟩
  | 2 => ⟨((996067233/8589934592), (-410777397/8589934592)), (27/8589934592), by norm_num⟩
  | 3 => ⟨((-115070199/4294967296), (189819463/17179869184)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((9970073/2147483648), (-263145651/137438953472)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((-353829273/549755813888), (583675731/2199023255552)), (47/2199023255552), by norm_num⟩
  | 6 => ⟨((81751921/1099511627776), (-134857729/4398046511104)), (23/8796093022208), by norm_num⟩
  | 7 => ⟨((-518090181/70368744177664), (427320021/140737488355328)), (19/70368744177664), by norm_num⟩
  | 8 => ⟨((1436450993/2251799813685248), (-74048917/281474976710656)), (55/2251799813685248), by norm_num⟩
  | 9 => ⟨((-885041739/18014398509481984), (91247641/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 10 => ⟨((490771349/144115188075855872), (-404787489/288230376151711744)), (21/144115188075855872), by norm_num⟩
  | 11 => ⟨((-989605169/4611686018427387904), (204056223/2305843009213693952)), (11/1152921504606846976), by norm_num⟩
  | 12 => ⟨((914589377/73786976294838206464), (-94293997/18446744073709551616)), (43/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-780240059/1180591620717411303424), (80442607/295147905179352825856)), (19/590295810358705651712), by norm_num⟩
  | 14 => ⟨((77260171/2361183241434822606848), (-254896303/18889465931478580854784)), (31/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-913965563/604462909807314587353088), (47114841/75557863725914323419136)), (47/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((633512653/9671406556917033397649408), (-522520307/19342813113834066795298816)), (67/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (-509515883555/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780967897116847/633825300114114700748351602688), (-604403439055/633825300114114700748351602688)), (11533/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946107804785127/19807040628566084398385987584), (-679913993115/39614081257132168796771975168)), (12975/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473036245865597/618970019642690137449562112), (-90295086221/309485009821345068724781056)), (27573/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886905442467561/77371252455336267181195264), (-722306775401/154742504910672534362390528)), (13787/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776004745416637/4835703278458516698824704), (-677105322937/9671406556917033397649408)), (6463/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260937371209341/604462909807314587353088), (-37025617763/37778931862957161709568)), (11311/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945641484625409/37778931862957161709568), (-240639671567/18889465931478580854784)), (18381/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300157039839045/4722366482869645213696), (-360912536529/2361183241434822606848)), (13787/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625046309985059/590295810358705651712), (-248089210687/147573952589676412928)), (18959/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827970882999575/73786976294838206464), (-620108571839/36893488147419103232)), (23701/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827713143723763/9223372036854775808), (-1394929599581/9223372036854775808)), (53335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399739771465545/288230376151711744), (-87158521033/72057594037927936)), (1667/36028797018963968), by norm_num⟩
  | 5 => ⟨((1198929451738887/144115188075855872), (-1219777005181/144115188075855872)), (23343/72057594037927936), by norm_num⟩
  | 4 => ⟨((749077336282025/18014398509481984), (-114298828641/2251799813685248)), (70049/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497394194495615/9007199254740992), (-2284429876275/9007199254740992)), (87597/9007199254740992), by norm_num⟩
  | 2 => ⟨((2244190919465707/4503599627370496), (-2282111311069/2251799813685248)), (175299/4503599627370496), by norm_num⟩
  | 1 => ⟨((1120196321909821/1125899906842624), (-6834751459009/2251799813685248)), (16451/140737488355328), by norm_num⟩
  | 0 => ⟨((1114505081509131/1125899906842624), (-6811617544295/1125899906842624)), (527505/2251799813685248), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114505081509131/1125899906842624), (-6811617544295/1125899906842624)), (2012271889693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((275796092314119/281474976710656), (-13485359258449/1125899906842624)), (262679/562949953421312), by norm_num⟩
  | 2 => ⟨((270191402064741/281474976710656), (-26426572126555/1125899906842624)), (2084205/2251799813685248), by norm_num⟩
  | 3 => ⟨((518410175356813/562949953421312), (-50734403875473/1125899906842624)), (4099149/2251799813685248), by norm_num⟩
  | 4 => ⟨((238125621425073/281474976710656), (-46720371944011/562949953421312)), (7919087/2251799813685248), by norm_num⟩
  | 5 => ⟨((1596109578100325/2251799813685248), (-316200544215751/2251799813685248)), (7356707/1125899906842624), by norm_num⟩
  | 6 => ⟨((1086945201019267/2251799813685248), (-448255403660709/2251799813685248)), (24990331/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-1739128909/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-1378227053/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-46856421579491/1125899906842624), (-798468659424865/2251799813685248)), (16422227/562949953421312), by norm_num⟩
  | 1 => ⟨((98184663/2147483648), (1673140491/4294967296)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((-215733755/8589934592), (-1838132705/8589934592)), (157/8589934592), by norm_num⟩
  | 3 => ⟨((79002585/8589934592), (336565863/4294967296)), (117/17179869184), by norm_num⟩
  | 4 => ⟨((-173586421/68719476736), (-1479021573/68719476736)), (131/68719476736), by norm_num⟩
  | 5 => ⟨((38140835/68719476736), (1299897021/274877906944)), (59/137438953472), by norm_num⟩
  | 6 => ⟨((-6983665/68719476736), (-238013807/274877906944)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((140294221/8796093022208), (149419939/1099511627776)), (113/8796093022208), by norm_num⟩
  | 8 => ⟨((-154128955/70368744177664), (-656618325/35184372088832)), (127/70368744177664), by norm_num⟩
  | 9 => ⟨((75256873/281474976710656), (320608427/140737488355328)), (63/281474976710656), by norm_num⟩
  | 10 => ⟨((-132285001/4503599627370496), (-1127117945/4503599627370496)), (113/4503599627370496), by norm_num⟩
  | 11 => ⟨((105694493/36028797018963968), (1801113637/72057594037927936)), (183/72057594037927936), by norm_num⟩
  | 12 => ⟨((-154823025/576460752303423488), (-82446899/36028797018963968)), (17/72057594037927936), by norm_num⟩
  | 13 => ⟨((209342127/9223372036854775808), (445918407/2305843009213693952)), (187/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-32855119/18446744073709551616), (-1119751867/73786976294838206464)), (119/73786976294838206464), by norm_num⟩
  | 15 => ⟨((154005493/1180591620717411303424), (656092353/590295810358705651712)), (71/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-169192327/18889465931478580854784), (-1441582243/18889465931478580854784)), (79/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (-2198323317505/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445094321597273/158456325028528675187087900672), (-1303043375085/316912650057057350374175801344)), (46229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945775509269597/19807040628566084398385987584), (-732892976989/9903520314283042199192993792)), (52015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945719331254617/1237940039285380274899124224), (-1557233522759/1237940039285380274899124224)), (13819/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443276086740235/38685626227668133590597632), (-1557048958403/77371252455336267181195264)), (27643/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387836720246489/2417851639229258349412352), (-364884325579/1208925819614629174706176)), (25921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39386167412367/18889465931478580854784), (-638449523603/151115727451828646838272)), (22687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118146250918439/4722366482869645213696), (-4149186573701/75557863725914323419136)), (73753/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649724723161229/2361183241434822606848), (-3111246533315/4722366482869645213696)), (27667/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812036377847851/295147905179352825856), (-4276918494389/590295810358705651712)), (38057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456688255255951/18446744073709551616), (-1336144984839/18446744073709551616)), (23797/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228292723292917/1152921504606846976), (-6010496275589/9223372036854775808)), (26787/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798793075922661/576460752303423488), (-1501950303829/288230376151711744)), (53613/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197726363075009/144115188075855872), (-5253794307487/144115188075855872)), (93911/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496346502559295/36028797018963968), (-3937314210299/18014398509481984)), (141043/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495127805242203/9007199254740992), (-9832676275723/9007199254740992)), (176613/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119819831375109/2251799813685248), (-2454191142511/562949953421312)), (177077/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116759872583663/1125899906842624), (-14685375305789/1125899906842624)), (266775/1125899906842624), by norm_num⟩
  | 0 => ⟨((553770350411805/562949953421312), (-7302927919861/281474976710656)), (538199/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((553770350411805/562949953421312), (-7302927919861/281474976710656)), (2053066257957076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((544361480284299/562949953421312), (-7183844547167/140737488355328)), (543387/562949953421312), by norm_num⟩
  | 2 => ⟨((1049840034488865/1125899906842624), (-111146171429599/1125899906842624)), (1106363/562949953421312), by norm_num⟩
  | 3 => ⟨((967946280098995/1125899906842624), (-103637721024579/562949953421312)), (4563363/1125899906842624), by norm_num⟩
  | 4 => ⟨((793993219866003/1125899906842624), (-356393124944811/1125899906842624)), (4763269/562949953421312), by norm_num⟩
  | 5 => ⟨((111779291086579/281474976710656), (-502662311442203/1125899906842624)), (19467449/1125899906842624), by norm_num⟩
  | 6 => ⟨((-46856421579491/1125899906842624), (-798468659424865/2251799813685248)), (16422227/562949953421312), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-1378227053/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-1739128909/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((870874006782243/4503599627370496), (-432746336400635/2251799813685248)), (17212327/1125899906842624), by norm_num⟩
  | 1 => ⟨((-17989989/67108864), (572122389/2147483648)), (47/2147483648), by norm_num⟩
  | 2 => ⟨((399030725/2147483648), (-396565021/2147483648)), (67/4294967296), by norm_num⟩
  | 3 => ⟨((-46097837/536870912), (733007803/8589934592)), (1/134217728), by norm_num⟩
  | 4 => ⟨((127810343/4294967296), (-127020573/4294967296)), (91/34359738368), by norm_num⟩
  | 5 => ⟨((-566984825/68719476736), (563481293/68719476736)), (13/17179869184), by norm_num⟩
  | 6 => ⟨((131001311/68719476736), (-520767293/274877906944)), (99/549755813888), by norm_num⟩
  | 7 => ⟨((-830200589/2199023255552), (825070585/2199023255552)), (81/2199023255552), by norm_num⟩
  | 8 => ⟨((287725599/4398046511104), (-285947675/4398046511104)), (29/4398046511104), by norm_num⟩
  | 9 => ⟨((-709106445/70368744177664), (352362355/35184372088832)), (73/70368744177664), by norm_num⟩
  | 10 => ⟨((786424213/562949953421312), (-781564713/562949953421312)), (83/562949953421312), by norm_num⟩
  | 11 => ⟨((-792883965/4503599627370496), (787984549/4503599627370496)), (43/2251799813685248), by norm_num⟩
  | 12 => ⟨((183195095/9007199254740992), (-364126179/18014398509481984)), (81/36028797018963968), by norm_num⟩
  | 13 => ⟨((-156284509/72057594037927936), (621275161/288230376151711744)), (71/288230376151711744), by norm_num⟩
  | 14 => ⟨((990428953/4611686018427387904), (-246077215/1152921504606846976)), (115/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-183070143/9223372036854775808), (727755639/36893488147419103232)), (87/36893488147419103232), by norm_num⟩
  | 16 => ⟨((253789107/147573952589676412928), (-1008883539/590295810358705651712)), (123/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-509515883555/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779963741320331/633825300114114700748351602688), (-150939191597/79228162514264337593543950336)), (2885/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1891085998732943/39614081257132168796771975168), (-1358295385963/39614081257132168796771975168)), (25967/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890944848238993/2475880078570760549798248448), (-1442997402543/2475880078570760549798248448)), (3449/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772610835544181/154742504910672534362390528), (-721391032841/77371252455336267181195264)), (55189/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550884535728089/9671406556917033397649408), (-1352379431203/9671406556917033397649408)), (51745/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629976563346599/302231454903657293676544), (-1183103291971/604462909807314587353088)), (22641/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944841871459077/37778931862957161709568), (-1922114113277/75557863725914323419136)), (73593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649478884862117/2361183241434822606848), (-1441210536479/4722366482869645213696)), (55203/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811698778370871/295147905179352825856), (-990527606613/295147905179352825856)), (75919/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825910306206511/73786976294838206464), (-1237702709327/36893488147419103232)), (94919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456348874100281/2305843009213693952), (-2783575408611/9223372036854775808)), (106813/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596642065535911/1152921504606846976), (-1391003281833/576460752303423488)), (106849/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598451382185675/72057594037927936), (-608122960763/36028797018963968)), (46767/72057594037927936), by norm_num⟩
  | 4 => ⟨((747558026232669/18014398509481984), (-911303147219/9007199254740992)), (140383/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493598388799387/9007199254740992), (-1137588145029/2251799813685248)), (175621/9007199254740992), by norm_num⟩
  | 2 => ⟨((559151679345763/1125899906842624), (-9082239278945/4503599627370496)), (351673/4503599627370496), by norm_num⟩
  | 1 => ⟨((278629358439317/281474976710656), (-6788638340729/1125899906842624)), (264293/1125899906842624), by norm_num⟩
  | 0 => ⟨((275796092314119/281474976710656), (-13485359258449/1125899906842624)), (530747/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((275796092314119/281474976710656), (-13485359258449/1125899906842624)), (2024639133933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((270191402064741/281474976710656), (-26426572126555/1125899906842624)), (131599/140737488355328), by norm_num⟩
  | 2 => ⟨((518410175356813/562949953421312), (-50734403875473/1125899906842624)), (4141197/2251799813685248), by norm_num⟩
  | 3 => ⟨((238125621425073/281474976710656), (-46720371944011/562949953421312)), (8000319/2251799813685248), by norm_num⟩
  | 4 => ⟨((1596109578100325/2251799813685248), (-316200544215751/2251799813685248)), (14864341/2251799813685248), by norm_num⟩
  | 5 => ⟨((1086945201019267/2251799813685248), (-448255403660709/2251799813685248)), (25246677/2251799813685248), by norm_num⟩
  | 6 => ⟨((870874006782243/4503599627370496), (-432746336400635/2251799813685248)), (17212327/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-1739128909/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-1009533069/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((238017885996525/4503599627370496), (967179842050285/4503599627370496)), (73140913/4503599627370496), by norm_num⟩
  | 1 => ⟨((-182664399/2147483648), (-742252305/2147483648)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((293987009/4294967296), (149326125/536870912)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-78858973/2147483648), (-640883005/4294967296)), (103/8589934592), by norm_num⟩
  | 4 => ⟨((126918621/8589934592), (515730703/8589934592)), (21/4294967296), by norm_num⟩
  | 5 => ⟨((-326828225/68719476736), (-664029237/34359738368)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((175336579/137438953472), (356237943/68719476736)), (15/34359738368), by norm_num⟩
  | 7 => ⟨((-20156667/68719476736), (-655248973/549755813888)), (7/68719476736), by norm_num⟩
  | 8 => ⟨((259527233/4398046511104), (1054582539/4398046511104)), (23/1099511627776), by norm_num⟩
  | 9 => ⟨((-185641319/17592186044416), (-1508697885/35184372088832)), (67/17592186044416), by norm_num⟩
  | 10 => ⟨((119511271/70368744177664), (485631115/70368744177664)), (11/17592186044416), by norm_num⟩
  | 11 => ⟨((-279775957/1125899906842624), (-284215683/281474976710656)), (105/1125899906842624), by norm_num⟩
  | 12 => ⟨((150094011/4503599627370496), (1219806655/9007199254740992)), (115/9007199254740992), by norm_num⟩
  | 13 => ⟨((-297313221/72057594037927936), (-604062485/36028797018963968)), (29/18014398509481984), by norm_num⟩
  | 14 => ⟨((68358167/144115188075855872), (1111086931/576460752303423488)), (109/576460752303423488), by norm_num⟩
  | 15 => ⟨((-58676387/1152921504606846976), (-476860115/2305843009213693952)), (95/4611686018427387904), by norm_num⟩
  | 16 => ⟨((377744007/73786976294838206464), (191869187/9223372036854775808)), (155/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (1731817698719/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779639421954063/633825300114114700748351602688), (2051429904451/633825300114114700748351602688)), (23101/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472680274929681/9903520314283042199192993792), (2307548027563/39614081257132168796771975168)), (51983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890557090070207/2475880078570760549798248448), (612848008919/618970019642690137449562112)), (55239/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772223017845561/154742504910672534362390528), (2450967144063/154742504910672534362390528)), (3453/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775260446717609/4835703278458516698824704), (574332581921/2417851639229258349412352)), (12951/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314908719135703/151115727451828646838272), (2009712753973/604462909807314587353088)), (22669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472291617037027/18889465931478580854784), (12753661153/295147905179352825856)), (36845/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298569710274993/4722366482869645213696), (2447962902693/4722366482869645213696)), (27641/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101428987952747/36893488147419103232), (1682373387683/295147905179352825856)), (19009/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825242868093285/73786976294838206464), (262758172041/4611686018427387904)), (47541/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824644283703313/9223372036854775808), (2363584674015/4611686018427387904)), (13377/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595890422765605/1152921504606846976), (147627301303/36028797018963968)), (53539/576460752303423488), by norm_num⟩
  | 5 => ⟨((149530574303105/18014398509481984), (4130083800793/144115188075855872)), (93763/144115188075855872), by norm_num⟩
  | 4 => ⟨((93382989735571/2251799813685248), (773521189163/4503599627370496)), (140783/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492361442163289/9007199254740992), (3861524998497/4503599627370496)), (88111/4503599627370496), by norm_num⟩
  | 2 => ⟨((558531956532133/1125899906842624), (15409660028201/4503599627370496)), (353175/4503599627370496), by norm_num⟩
  | 1 => ⟨((2225304138026327/2251799813685248), (5755887514409/562949953421312)), (265797/1125899906842624), by norm_num⟩
  | 0 => ⟨((274857290147419/281474976710656), (45684299084491/2251799813685248)), (133817/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((274857290147419/281474976710656), (45684299084491/2251799813685248)), (510471345067882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2146234683947073/2251799813685248), (44610227151933/1125899906842624)), (2134173/2251799813685248), by norm_num⟩
  | 2 => ⟨((2042083404201735/2251799813685248), (85037769512507/1125899906842624)), (4237365/2251799813685248), by norm_num⟩
  | 3 => ⟨((1839052883641611/2251799813685248), (308471857571787/2251799813685248)), (8325541/2251799813685248), by norm_num⟩
  | 4 => ⟨((729851872697637/1125899906842624), (251930058676599/1125899906842624)), (7940007/1125899906842624), by norm_num⟩
  | 5 => ⟨((416746638634405/1125899906842624), (653243237685577/2251799813685248)), (27694667/2251799813685248), by norm_num⟩
  | 6 => ⟨((238017885996525/4503599627370496), (967179842050285/4503599627370496)), (73140913/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-1009533069/33554432)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-56363879/33554432), (-561947877/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-408365456464377/4503599627370496), (-733532699531725/4503599627370496)), (18634485/562949953421312), by norm_num⟩
  | 1 => ⟨((348898255/2147483648), (1253427659/4294967296)), (257/4294967296), by norm_num⟩
  | 2 => ⟨((-78142719/536870912), (-1122920439/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((746735769/8589934592), (1341335553/8589934592)), (279/8589934592), by norm_num⟩
  | 4 => ⟨((-668985443/17179869184), (-1201675339/17179869184)), (63/4294967296), by norm_num⟩
  | 5 => ⟨((479464401/34359738368), (861245267/34359738368)), (91/17179869184), by norm_num⟩
  | 6 => ⟨((-286361627/68719476736), (-257190727/34359738368)), (219/137438953472), by norm_num⟩
  | 7 => ⟨((293194947/274877906944), (526655909/274877906944)), (113/274877906944), by norm_num⟩
  | 8 => ⟨((-525334823/2199023255552), (-117955089/274877906944)), (51/549755813888), by norm_num⟩
  | 9 => ⟨((209171921/4398046511104), (751456525/8796093022208)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((-37478577/4398046511104), (-269285869/17592186044416)), (237/70368744177664), by norm_num⟩
  | 11 => ⟨((390706009/281474976710656), (701811645/281474976710656)), (39/70368744177664), by norm_num⟩
  | 12 => ⟨((-233350397/1125899906842624), (-838318441/2251799813685248)), (47/562949953421312), by norm_num⟩
  | 13 => ⟨((514594195/18014398509481984), (924347695/18014398509481984)), (209/18014398509481984), by norm_num⟩
  | 14 => ⟨((-526873727/144115188075855872), (-7393789/1125899906842624)), (27/18014398509481984), by norm_num⟩
  | 15 => ⟨((251741597/576460752303423488), (452194695/576460752303423488)), (13/72057594037927936), by norm_num⟩
  | 16 => ⟨((-225530195/4611686018427387904), (-810224127/9223372036854775808)), (47/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49430864790015/316912650057057350374175801344), (-2707839210765/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779372468871577/633825300114114700748351602688), (-3206675158023/633825300114114700748351602688)), (92515/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236302579161075/4951760157141521099596496896), (-3606965009181/39614081257132168796771975168)), (26025/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((29534963386537/38685626227668133590597632), (-957935583229/618970019642690137449562112)), (55315/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771903373451099/154742504910672534362390528), (-3831002154529/154742504910672534362390528)), (110657/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550221002704223/9671406556917033397649408), (-448847272541/1208925819614629174706176)), (12971/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259372248202661/604462909807314587353088), (-3141144680625/604462909807314587353088)), (90825/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888739277529383/75557863725914323419136), (-2551443084491/37778931862957161709568)), (36911/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298248950531837/4722366482869645213696), (-3825875170825/4722366482869645213696)), (110779/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622422167220347/590295810358705651712), (-5258483442347/590295810358705651712)), (38099/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824689926116769/73786976294838206464), (-1642490677899/18446744073709551616)), (190607/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824020999368411/9223372036854775808), (-7386889638803/9223372036854775808)), (214587/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199408201298531/144115188075855872), (-7381493539993/1152921504606846976)), (53695/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195696168285923/144115188075855872), (-6452738872837/144115188075855872)), (94075/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493301775280985/36028797018963968), (-9666978957743/36028797018963968)), (282661/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491322900296081/9007199254740992), (-6031256097511/4503599627370496)), (44261/1125899906842624), by norm_num⟩
  | 2 => ⟨((558008231854341/1125899906842624), (-12030724712435/2251799813685248)), (177617/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111058772592863/1125899906842624), (-17966722759567/1125899906842624)), (66965/140737488355328), by norm_num⟩
  | 0 => ⟨((137019369219727/140737488355328), (-17808308129511/562949953421312)), (1082949/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137019369219727/140737488355328), (-17808308129511/562949953421312)), (4131122593406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((266517283641145/281474976710656), (-69351334183697/1125899906842624)), (1088597/562949953421312), by norm_num⟩
  | 2 => ⟨((1005146003867997/1125899906842624), (-131331952982295/1125899906842624)), (4391209/1125899906842624), by norm_num⟩
  | 3 => ⟨((882023704933541/1125899906842624), (-234492936571111/1125899906842624)), (8864931/1125899906842624), by norm_num⟩
  | 4 => ⟨((642134238016243/1125899906842624), (-734801832518873/2251799813685248)), (35164203/2251799813685248), by norm_num⟩
  | 5 => ⟨((246338901601131/1125899906842624), (-209539681080815/562949953421312)), (63059779/2251799813685248), by norm_num⟩
  | 6 => ⟨((-408365456464377/4503599627370496), (-733532699531725/4503599627370496)), (18634485/562949953421312), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56363879/33554432), (-561947877/16777216)), (1/16777216), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-3825815/2097152), (-610294013/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((178378983671113/4503599627370496), (1408675926568299/9007199254740992)), (13370195/562949953421312), by norm_num⟩
  | 1 => ⟨((-331029391/4294967296), (-653542705/2147483648)), (25/536870912), by norm_num⟩
  | 2 => ⟨((161038363/2147483648), (1271735383/4294967296)), (49/1073741824), by norm_num⟩
  | 3 => ⟨((-104455395/2147483648), (-824894263/4294967296)), (1/33554432), by norm_num⟩
  | 4 => ⟨((406521627/17179869184), (802585059/8589934592)), (251/17179869184), by norm_num⟩
  | 5 => ⟨((-4944091/536870912), (-624703365/17179869184)), (197/34359738368), by norm_num⟩
  | 6 => ⟨((205242813/68719476736), (810411079/68719476736)), (129/68719476736), by norm_num⟩
  | 7 => ⟨((-114109735/137438953472), (-901135511/274877906944)), (145/274877906944), by norm_num⟩
  | 8 => ⟨((222047291/1099511627776), (54797773/68719476736)), (143/1099511627776), by norm_num⟩
  | 9 => ⟨((-384074735/8796093022208), (-1516537495/8796093022208)), (249/8796093022208), by norm_num⟩
  | 10 => ⟨((149474985/17592186044416), (1180418281/35184372088832)), (195/35184372088832), by norm_num⟩
  | 11 => ⟨((-105769051/70368744177664), (-208817083/35184372088832)), (139/140737488355328), by norm_num⟩
  | 12 => ⟨((34302845/140737488355328), (135446427/140737488355328)), (91/562949953421312), by norm_num⟩
  | 13 => ⟨((-82154159/2251799813685248), (-1297558533/9007199254740992)), (55/2251799813685248), by norm_num⟩
  | 14 => ⟨((365404827/72057594037927936), (360704617/18014398509481984)), (123/36028797018963968), by norm_num⟩
  | 15 => ⟨((-379223979/576460752303423488), (-748692027/288230376151711744)), (129/288230376151711744), by norm_num⟩
  | 16 => ⟨((368967895/4611686018427387904), (728443707/2305843009213693952)), (253/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790799712358623/5070602400912917605986812821504), (1723034757789/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779152839208759/633825300114114700748351602688), (254995560635/79228162514264337593543950336)), (92401/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890173777826301/39614081257132168796771975168), (2294589871037/39614081257132168796771975168)), (25991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889975661343499/2475880078570760549798248448), (2437547760447/2475880078570760549798248448)), (110477/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771641702496221/154742504910672534362390528), (2437037158763/154742504910672534362390528)), (55247/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549976030746263/9671406556917033397649408), (1142089973575/4835703278458516698824704)), (103605/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259158242127101/604462909807314587353088), (999057602637/302231454903657293676544)), (90673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236049020376571/9444732965739290427392), (3245920791605/75557863725914323419136)), (9211/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324497294739985/1180591620717411303424), (152096970483/295147905179352825856)), (110561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622065897627109/590295810358705651712), (209043073665/36893488147419103232)), (76035/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912122981193411/36893488147419103232), (4178696195405/73786976294838206464)), (95079/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455880856608145/2305843009213693952), (4698057554787/9223372036854775808)), (107013/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594770392318065/1152921504606846976), (2347170180283/576460752303423488)), (107075/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195265497631419/144115188075855872), (4103369252597/144115188075855872)), (187519/144115188075855872), by norm_num⟩
  | 4 => ⟨((746330524727007/18014398509481984), (3073352474843/18014398509481984)), (70389/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490531210448375/9007199254740992), (3834394494893/4503599627370496)), (176215/4503599627370496), by norm_num⟩
  | 2 => ⟨((2230477108805303/4503599627370496), (7646937517595/2251799813685248)), (44145/281474976710656), by norm_num⟩
  | 1 => ⟨((1109926200603257/1125899906842624), (11415906327083/1125899906842624)), (1063135/2251799813685248), by norm_num⟩
  | 0 => ⟨((8547078307943/8796093022208), (45229168054333/2251799813685248)), (2140941/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((8547078307943/8796093022208), (45229168054333/2251799813685248)), (8167041787154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1062600248238117/1125899906842624), (87897488166049/2251799813685248)), (4246669/2251799813685248), by norm_num⟩
  | 2 => ⟨((2002287749734735/2251799813685248), (41477884569097/562949953421312)), (8347363/2251799813685248), by norm_num⟩
  | 3 => ⟨((1768198740405925/2251799813685248), (36881902046921/281474976710656)), (16074917/2251799813685248), by norm_num⟩
  | 4 => ⟨((168724434693889/281474976710656), (115844281266569/562949953421312)), (29457891/2251799813685248), by norm_num⟩
  | 5 => ⟨((5576197389885/17592186044416), (555523936021181/2251799813685248)), (47439601/2251799813685248), by norm_num⟩
  | 6 => ⟨((178378983671113/4503599627370496), (1408675926568299/9007199254740992)), (13370195/562949953421312), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3825815/2097152), (-610294013/16777216)), (1/16777216), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-652173341/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((248081797342633/4503599627370496), (-73891842135497/562949953421312)), (177806531/9007199254740992), by norm_num⟩
  | 1 => ⟨((-491973491/4294967296), (1172285203/4294967296)), (179/4294967296), by norm_num⟩
  | 2 => ⟨((511515057/4294967296), (-1218849275/4294967296)), (189/4294967296), by norm_num⟩
  | 3 => ⟨((-88638805/1073741824), (844841939/4294967296)), (133/4294967296), by norm_num⟩
  | 4 => ⟨((368638427/8589934592), (-27449991/268435456)), (35/2147483648), by norm_num⟩
  | 5 => ⟨((-613249647/34359738368), (1461264681/34359738368)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((53134033/8589934592), (-506435747/34359738368)), (83/34359738368), by norm_num⟩
  | 7 => ⟨((-505093099/274877906944), (300886723/68719476736)), (25/34359738368), by norm_num⟩
  | 8 => ⟨((262577893/549755813888), (-625676351/549755813888)), (211/1099511627776), by norm_num⟩
  | 9 => ⟨((-485347003/4398046511104), (1156495463/4398046511104)), (197/4398046511104), by norm_num⟩
  | 10 => ⟨((6307817/274877906944), (-961945883/17592186044416)), (83/8796093022208), by norm_num⟩
  | 11 => ⟨((-76315559/17592186044416), (363692769/35184372088832)), (127/70368744177664), by norm_num⟩
  | 12 => ⟨((105795829/140737488355328), (-504185235/281474976710656)), (179/562949953421312), by norm_num⟩
  | 13 => ⟨((-541529211/4503599627370496), (645183829/2251799813685248)), (29/562949953421312), by norm_num⟩
  | 14 => ⟨((80434167/4503599627370496), (-766641175/18014398509481984)), (35/4503599627370496), by norm_num⟩
  | 15 => ⟨((-356817383/144115188075855872), (425116135/72057594037927936)), (157/144115188075855872), by norm_num⟩
  | 16 => ⟨((370990445/1152921504606846976), (-884004151/1152921504606846976)), (83/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (-1528547660371/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778960270603985/633825300114114700748351602688), (-452332573163/158456325028528675187087900672)), (46189/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889957201784049/39614081257132168796771975168), (-1017573719391/19807040628566084398385987584)), (103937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944872814325511/1237940039285380274899124224), (-540478499071/618970019642690137449562112)), (110447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771411759040919/154742504910672534362390528), (-1080715104299/77371252455336267181195264)), (55231/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549760553538619/9671406556917033397649408), (-2025826931059/9671406556917033397649408)), (51787/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258969794315223/604462909807314587353088), (-1772084826943/604462909807314587353088)), (90643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888086112886419/75557863725914323419136), (-1439337453973/37778931862957161709568)), (147323/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648879898329561/2361183241434822606848), (-2158163934411/4722366482869645213696)), (110519/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405437687292267/147573952589676412928), (-2966107363279/590295810358705651712)), (152005/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823852404865811/73786976294838206464), (-926395797759/18446744073709551616)), (95035/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911540596812583/4611686018427387904), (-4165962663323/9223372036854775808)), (53479/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594328808139969/1152921504606846976), (-1040610550793/288230376151711744)), (214025/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298719960081087/36028797018963968), (-1819089972867/72057594037927936)), (187395/144115188075855872), by norm_num⟩
  | 4 => ⟨((373021004761183/9007199254740992), (-2724682393235/18014398509481984)), (281339/36028797018963968), by norm_num⟩
  | 3 => ⟨((744906232413857/4503599627370496), (-6797891854199/9007199254740992)), (44013/1125899906842624), by norm_num⟩
  | 2 => ⟨((1114523612733359/2251799813685248), (-13554420633375/4503599627370496)), (705505/4503599627370496), by norm_num⟩
  | 1 => ⟨((277215816078055/281474976710656), (-20228500413887/2251799813685248)), (1061507/2251799813685248), by norm_num⟩
  | 0 => ⟨((2183875708300049/2251799813685248), (-10011534520009/562949953421312)), (267007/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2183875708300049/2251799813685248), (-10011534520009/562949953421312)), (1018550873876476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2117288307402949/2251799813685248), (-38838171862663/1125899906842624)), (4219223/2251799813685248), by norm_num⟩
  | 2 => ⟨((994066198754131/1125899906842624), (-73036338901853/1125899906842624)), (8225461/2251799813685248), by norm_num⟩
  | 3 => ⟨((1745862655698185/2251799813685248), (-257937514131909/2251799813685248)), (7795907/1125899906842624), by norm_num⟩
  | 4 => ⟨((331013511197239/562949953421312), (-24997974436365/140737488355328)), (6937313/562949953421312), by norm_num⟩
  | 5 => ⟨((353749260925391/1125899906842624), (-470360378756141/2251799813685248)), (42490733/2251799813685248), by norm_num⟩
  | 6 => ⟨((248081797342633/4503599627370496), (-73891842135497/562949953421312)), (177806531/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-652173341/16777216)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile008Terms0

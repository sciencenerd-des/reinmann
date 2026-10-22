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
namespace Reinmann.XiBand97.Tile028Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30757/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30757/1280))
  have he : value ((69/80), (30757/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1117736289/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-722817185630829/2251799813685248), (251419102867683/562949953421312)), (54647159/1125899906842624), by norm_num⟩
  | 1 => ⟨((477808661/2147483648), (-166197245/536870912)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((-165595863/2147483648), (460796607/4294967296)), (105/8589934592), by norm_num⟩
  | 3 => ⟨((76521537/4294967296), (-106466623/4294967296)), (99/34359738368), by norm_num⟩
  | 4 => ⟨((-424325501/137438953472), (1180752633/274877906944)), (139/274877906944), by norm_num⟩
  | 5 => ⟨((470592039/1099511627776), (-654748287/1099511627776)), (79/1099511627776), by norm_num⟩
  | 6 => ⟨((-869838787/17592186044416), (1210231811/17592186044416)), (37/4398046511104), by norm_num⟩
  | 7 => ⟨((86132329/17592186044416), (-958707163/140737488355328)), (119/140737488355328), by norm_num⟩
  | 8 => ⟨((-59702381/140737488355328), (664525167/1125899906842624)), (21/281474976710656), by norm_num⟩
  | 9 => ⟨((294275819/9007199254740992), (-409434441/9007199254740992)), (53/9007199254740992), by norm_num⟩
  | 10 => ⟨((-326362327/144115188075855872), (908154651/288230376151711744)), (15/36028797018963968), by norm_num⟩
  | 11 => ⟨((658086187/4611686018427387904), (-915614307/4611686018427387904)), (123/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-152050195/18446744073709551616), (846207301/73786976294838206464)), (29/18446744073709551616), by norm_num⟩
  | 13 => ⟨((518858653/1180591620717411303424), (-721903021/1180591620717411303424)), (101/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-822046657/37778931862957161709568), (1143737243/37778931862957161709568)), (81/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((75973243/75557863725914323419136), (-52851883/37778931862957161709568)), (61/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-842570227/19342813113834066795298816), (586146139/9671406556917033397649408)), (171/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (2857913427241/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781042300639991/633825300114114700748351602688), (3390435137471/633825300114114700748351602688)), (46267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892298948266617/39614081257132168796771975168), (1907010383233/19807040628566084398385987584)), (52061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892233086006901/2475880078570760549798248448), (1013037036467/618970019642690137449562112)), (55327/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886949243561579/77371252455336267181195264), (4051868006315/154742504910672534362390528)), (55341/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552091086352993/9671406556917033397649408), (1899164256847/4835703278458516698824704)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630504117933413/302231454903657293676544), (3323239601619/604462909807314587353088)), (45425/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891397128134787/75557863725914323419136), (5399705663507/75557863725914323419136)), (73843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650120893786501/2361183241434822606848), (4049290170379/4722366482869645213696)), (27703/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((203145177810365/73786976294838206464), (5566978813469/590295810358705651712)), (76223/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828112650930361/73786976294838206464), (6957530025639/73786976294838206464)), (95337/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228483714398165/1152921504606846976), (7825579034967/9223372036854775808)), (13417/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599112012359307/1152921504606846976), (3911762220727/576460752303423488)), (53719/576460752303423488), by norm_num⟩
  | 5 => ⟨((299764791099887/36028797018963968), (3421635005837/72057594037927936)), (94123/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498341051912191/36028797018963968), (641266945853/2251799813685248)), (141413/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497612851230233/9007199254740992), (1602151979765/1125899906842624)), (177167/9007199254740992), by norm_num⟩
  | 2 => ⟨((280573167292221/562949953421312), (12805003707433/2251799813685248)), (88885/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120438619015097/1125899906842624), (9588439587955/562949953421312)), (67041/281474976710656), by norm_num⟩
  | 0 => ⟨((1114776215725313/1125899906842624), (38230678336247/1125899906842624)), (542373/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114776215725313/1125899906842624), (38230678336247/1125899906842624)), (2068988804343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102464276652881/1125899906842624), (37852966024137/562949953421312)), (69429/70368744177664), by norm_num⟩
  | 2 => ⟨((1074425964330017/1125899906842624), (74130111483879/562949953421312)), (1162437/562949953421312), by norm_num⟩
  | 3 => ⟨((1005782176754655/1125899906842624), (282964110869551/1125899906842624)), (5049457/1125899906842624), by norm_num⟩
  | 4 => ⟨((827364043087485/1125899906842624), (505551617233775/1125899906842624)), (2889897/281474976710656), by norm_num⟩
  | 5 => ⟨((761966173901357/2251799813685248), (1486012131209523/2251799813685248)), (54740057/2251799813685248), by norm_num⟩
  | 6 => ⟨((-722817185630829/2251799813685248), (251419102867683/562949953421312)), (54647159/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1117736289/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1771570105/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((32778312378435/281474976710656), (-1665365827336835/4503599627370496)), (123922505/4503599627370496), by norm_num⟩
  | 1 => ⟨((-68684877/536870912), (436208573/1073741824)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((37729025/536870912), (-479224099/2147483648)), (19/1073741824), by norm_num⟩
  | 3 => ⟨((-27633047/1073741824), (1403950625/17179869184)), (57/8589934592), by norm_num⟩
  | 4 => ⟨((30358005/4294967296), (-771198705/34359738368)), (1/536870912), by norm_num⟩
  | 5 => ⟨((-213450735/137438953472), (1355597399/274877906944)), (115/274877906944), by norm_num⟩
  | 6 => ⟨((156333067/549755813888), (-992850641/1099511627776)), (43/549755813888), by norm_num⟩
  | 7 => ⟨((-196285061/4398046511104), (1246580475/8796093022208)), (111/8796093022208), by norm_num⟩
  | 8 => ⟨((53910295/8796093022208), (-1369508629/70368744177664)), (31/17592186044416), by norm_num⟩
  | 9 => ⟨((-52645789/70368744177664), (668692893/281474976710656)), (31/140737488355328), by norm_num⟩
  | 10 => ⟨((370158789/4503599627370496), (-73463423/281474976710656)), (111/4503599627370496), by norm_num⟩
  | 11 => ⟨((-295753451/36028797018963968), (469572767/18014398509481984)), (91/36028797018963968), by norm_num⟩
  | 12 => ⟨((433224501/576460752303423488), (-687837883/288230376151711744)), (17/72057594037927936), by norm_num⟩
  | 13 => ⟨((-292889699/4611686018427387904), (465025939/2305843009213693952)), (47/2305843009213693952), by norm_num⟩
  | 14 => ⟨((367739683/73786976294838206464), (-583866527/36893488147419103232)), (15/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-430936891/1180591620717411303424), (1368411609/1180591620717411303424)), (143/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((118358141/4722366482869645213696), (-751676905/9444732965739290427392)), (5/590295810358705651712), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-1648729207203/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780506118461723/633825300114114700748351602688), (-1954814647483/633825300114114700748351602688)), (46197/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891696035760451/39614081257132168796771975168), (-2198977489335/39614081257132168796771975168)), (25989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891592844949815/2475880078570760549798248448), (-2336187338415/2475880078570760549798248448)), (55233/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55414332615841/4835703278458516698824704), (-2335932823467/154742504910672534362390528)), (55241/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387872913897181/2417851639229258349412352), (-2189666615895/9671406556917033397649408)), (51797/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630242078162395/302231454903657293676544), (-957843950415/302231454903657293676544)), (45331/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59079571584499/2361183241434822606848), (-3112485899523/75557863725914323419136)), (73679/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299604352215349/4722366482869645213696), (-2333920891069/4722366482869645213696)), (55273/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624286074282201/590295810358705651712), (-3208420555077/590295810358705651712)), (76023/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827020153371685/73786976294838206464), (-4009444814549/73786976294838206464)), (47531/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913321487653083/4611686018427387904), (-1127284853019/2305843009213693952)), (6687/576460752303423488), by norm_num⟩
  | 6 => ⟨((1597888171268233/1152921504606846976), (-2253641107023/576460752303423488)), (107051/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197991563129077/144115188075855872), (-3941783012449/144115188075855872)), (93735/144115188075855872), by norm_num⟩
  | 4 => ⟨((374186541434553/9007199254740992), (-2954248863711/18014398509481984)), (140735/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495630637844795/9007199254740992), (-3689157579503/4503599627370496)), (88075/4503599627370496), by norm_num⟩
  | 2 => ⟨((35010235338903/70368744177664), (-1841839858699/562949953421312)), (176497/2251799813685248), by norm_num⟩
  | 1 => ⟨((558766770738339/562949953421312), (-11023666591415/1125899906842624)), (265615/1125899906842624), by norm_num⟩
  | 0 => ⟨((277284058195749/281474976710656), (-5484485925487/281474976710656)), (66839/140737488355328), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277284058195749/281474976710656), (-5484485925487/281474976710656)), (254970551073980287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((546097349340163/562949953421312), (-10805653364347/281474976710656)), (268585/281474976710656), by norm_num⟩
  | 2 => ⟨((1057839207795405/1125899906842624), (-83857381982831/1125899906842624)), (541711/281474976710656), by norm_num⟩
  | 3 => ⟨((493823528307489/562949953421312), (-157576399083785/1125899906842624)), (1098623/281474976710656), by norm_num⟩
  | 4 => ⟨((844316960250795/1125899906842624), (-552908356422277/2251799813685248)), (2234957/281474976710656), by norm_num⟩
  | 5 => ⟨((141319004657691/281474976710656), (-414628245330313/1125899906842624)), (8899105/562949953421312), by norm_num⟩
  | 6 => ⟨((32778312378435/281474976710656), (-1665365827336835/4503599627370496)), (123922505/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1771570105/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1117736289/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-434248513366011/4503599627370496), (-645634828617343/2251799813685248)), (233582347/4503599627370496), by norm_num⟩
  | 1 => ⟨((71763547/536870912), (426788293/1073741824)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-198970801/2147483648), (-147913551/536870912)), (109/2147483648), by norm_num⟩
  | 3 => ⟨((367776133/8589934592), (546804591/4294967296)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((-509845979/34359738368), (-758032121/17179869184)), (285/34359738368), by norm_num⟩
  | 5 => ⟨((141359321/34359738368), (210171131/17179869184)), (5/2147483648), by norm_num⟩
  | 6 => ⟨((-130643753/137438953472), (-776957477/274877906944)), (149/274877906944), by norm_num⟩
  | 7 => ⟨((206983655/1099511627776), (615481011/1099511627776)), (119/1099511627776), by norm_num⟩
  | 8 => ⟨((-143470137/4398046511104), (-853237855/8796093022208)), (83/4398046511104), by norm_num⟩
  | 9 => ⟨((353585497/70368744177664), (1051412291/70368744177664)), (103/35184372088832), by norm_num⟩
  | 10 => ⟨((-392138865/562949953421312), (-145756693/70368744177664)), (231/562949953421312), by norm_num⟩
  | 11 => ⟨((395359925/4503599627370496), (587815801/2251799813685248)), (235/4503599627370496), by norm_num⟩
  | 12 => ⟨((-91347539/9007199254740992), (-1086514307/36028797018963968)), (219/36028797018963968), by norm_num⟩
  | 13 => ⟨((311715885/288230376151711744), (926909943/288230376151711744)), (47/72057594037927936), by norm_num⟩
  | 14 => ⟨((-493862827/4611686018427387904), (-734268587/2305843009213693952)), (75/1152921504606846976), by norm_num⟩
  | 15 => ⟨((365140935/36893488147419103232), (1085773229/36893488147419103232)), (7/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-506192819/590295810358705651712), (-1505201305/590295810358705651712)), (313/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-2468723529405/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780120450042689/633825300114114700748351602688), (-731460988901/158456325028528675187087900672)), (11561/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945631026075637/19807040628566084398385987584), (-3291215764103/39614081257132168796771975168)), (104067/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472782900214583/618970019642690137449562112), (-3496489089717/2475880078570760549798248448)), (110593/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443199311532477/38685626227668133590597632), (-3496007963089/154742504910672534362390528)), (13827/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551058932367739/9671406556917033397649408), (-3276996284189/9671406556917033397649408)), (103729/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260105360610397/604462909807314587353088), (-2866860585247/604462909807314587353088)), (22697/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889930442443061/75557863725914323419136), (-4657690057499/75557863725914323419136)), (147579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((10149548430881/36893488147419103232), (-873107246691/1180591620717411303424)), (55363/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((12684767035521/4611686018427387904), (-2400363637057/295147905179352825856)), (38079/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456556159240705/18446744073709551616), (-374929083997/4611686018427387904)), (190497/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114109195483367/576460752303423488), (-1686478390477/2305843009213693952)), (107225/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596991210817763/1152921504606846976), (-3371200716129/576460752303423488)), (107313/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197205472997003/144115188075855872), (-5895650532811/144115188075855872)), (46999/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495564536685903/36028797018963968), (-69027933033/281474976710656)), (141195/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494149249923723/9007199254740992), (-5515323030153/4503599627370496)), (353681/9007199254740992), by norm_num⟩
  | 2 => ⟨((559419820384907/1125899906842624), (-5504958057063/1125899906842624)), (354723/2251799813685248), by norm_num⟩
  | 1 => ⟨((278821384815661/281474976710656), (-16463066617237/1125899906842624)), (267347/562949953421312), by norm_num⟩
  | 0 => ⟨((1104576088792015/1125899906842624), (-32719008420087/1125899906842624)), (1079847/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104576088792015/1125899906842624), (-32719008420087/1125899906842624)), (4119289402488326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082705305338891/1125899906842624), (-64198663007553/1125899906842624)), (1090777/562949953421312), by norm_num⟩
  | 2 => ⟨((1037507244451973/1125899906842624), (-30867856286117/281474976710656)), (555563/140737488355328), by norm_num⟩
  | 3 => ⟨((942513702162913/1125899906842624), (-14222234286953/70368744177664)), (9165957/1125899906842624), by norm_num⟩
  | 4 => ⟨((1486012131209543/2251799813685248), (-380983086950675/1125899906842624)), (38102167/2251799813685248), by norm_num⟩
  | 5 => ⟨((180704296407715/562949953421312), (-62854775716921/140737488355328)), (38037505/1125899906842624), by norm_num⟩
  | 6 => ⟨((-434248513366011/4503599627370496), (-645634828617343/2251799813685248)), (233582347/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1117736289/33554432)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1297651647/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((39478581921665/281474976710656), (-464754910672347/2251799813685248)), (35099771/1125899906842624), by norm_num⟩
  | 1 => ⟨((-484758961/2147483648), (44583927/134217728)), (109/2147483648), by norm_num⟩
  | 2 => ⟨((390094725/2147483648), (-1148080999/4294967296)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-837110987/8589934592), (1231843391/8589934592)), (193/8589934592), by norm_num⟩
  | 4 => ⟨((84204885/2147483648), (-61955483/1073741824)), (157/17179869184), by norm_num⟩
  | 5 => ⟨((-216836055/17179869184), (1276332841/68719476736)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((14541007/4294967296), (-684726155/137438953472)), (111/137438953472), by norm_num⟩
  | 7 => ⟨((-427937791/549755813888), (1259456267/1099511627776)), (103/549755813888), by norm_num⟩
  | 8 => ⟨((688739305/4398046511104), (-1013508333/4398046511104)), (21/549755813888), by norm_num⟩
  | 9 => ⟨((-246329589/8796093022208), (724968327/17592186044416)), (61/8796093022208), by norm_num⟩
  | 10 => ⟨((634323487/140737488355328), (-933433209/140737488355328)), (159/140737488355328), by norm_num⟩
  | 11 => ⟨((-92809479/140737488355328), (1092583851/1125899906842624)), (47/281474976710656), by norm_num⟩
  | 12 => ⟨((199161459/2251799813685248), (-36634289/281474976710656)), (51/2251799813685248), by norm_num⟩
  | 13 => ⟨((-394508311/36028797018963968), (1161070545/72057594037927936)), (51/18014398509481984), by norm_num⟩
  | 14 => ⟨((362820933/288230376151711744), (-533905987/288230376151711744)), (189/576460752303423488), by norm_num⟩
  | 15 => ⟨((-622866949/4611686018427387904), (114571805/576460752303423488)), (41/1152921504606846976), by norm_num⟩
  | 16 => ⟨((501232841/36893488147419103232), (-737584827/36893488147419103232)), (67/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-634320347557/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779826736088633/633825300114114700748351602688), (-375767818105/158456325028528675187087900672)), (23087/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945465930673969/19807040628566084398385987584), (-422686513959/9903520314283042199192993792)), (103901/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890781068114183/2475880078570760549798248448), (-224520391173/309485009821345068724781056)), (55203/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886223522568175/77371252455336267181195264), (-1795876806769/154742504910672534362390528)), (55209/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775365485653715/4835703278458516698824704), (-6575509151/37778931862957161709568)), (51765/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629909373462875/302231454903657293676544), (-736304973487/302231454903657293676544)), (90603/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889465355389345/75557863725914323419136), (-598105275063/18889465931478580854784)), (36813/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298793961251363/4722366482869645213696), (-448454287199/1180591620717411303424)), (110461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623172291179337/590295810358705651712), (-2465688472725/590295810358705651712)), (151919/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825628680982199/73786976294838206464), (-3080895854467/73786976294838206464)), (189951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825078608683235/9223372036854775808), (-1732169131127/4611686018427387904)), (213767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596325103878393/1152921504606846976), (-216390770453/72057594037927936)), (106929/576460752303423488), by norm_num⟩
  | 5 => ⟨((598312670031567/72057594037927936), (-3027125528609/144115188075855872)), (187227/144115188075855872), by norm_num⟩
  | 4 => ⟨((373674937774163/9007199254740992), (-4536001323615/36028797018963968)), (70261/9007199254740992), by norm_num⟩
  | 3 => ⟨((373269431330151/2251799813685248), (-1415451858107/2251799813685248)), (175831/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235564537379741/4503599627370496), (-11299064071867/4503599627370496)), (704395/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227469490231737/2251799813685248), (-16887330576307/2251799813685248)), (1059277/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203229706323613/2251799813685248), (-33530266888605/2251799813685248)), (532329/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203229706323613/2251799813685248), (-33530266888605/2251799813685248)), (2030673982860374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2155207949896193/2251799813685248), (-32807037118025/1125899906842624)), (4230189/2251799813685248), by norm_num⟩
  | 2 => ⟨((2060847537314235/2251799813685248), (-125599063965799/2251799813685248)), (4171995/1125899906842624), by norm_num⟩
  | 3 => ⟨((939541210872599/1125899906842624), (-114948282742451/1125899906842624)), (4050913/562949953421312), by norm_num⟩
  | 4 => ⟨((386146483332133/562949953421312), (-191844138362939/1125899906842624)), (15175933/1125899906842624), by norm_num⟩
  | 5 => ⟨((994106580049835/2251799813685248), (-65796203487107/281474976710656)), (12995543/562949953421312), by norm_num⟩
  | 6 => ⟨((39478581921665/281474976710656), (-464754910672347/2251799813685248)), (35099771/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1297651647/33554432)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1444653197/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((8990971085507/70368744177664), (96100075088221/562949953421312)), (29352879/2251799813685248), by norm_num⟩
  | 1 => ⟨((-245813867/1073741824), (-328422965/1073741824)), (13/536870912), by norm_num⟩
  | 2 => ⟨((110109831/536870912), (1176909915/4294967296)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((-526107553/4294967296), (-351456581/2147483648)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((471329095/8589934592), (629725657/8589934592)), (53/8589934592), by norm_num⟩
  | 5 => ⟨((-675606695/34359738368), (-902653527/34359738368)), (39/17179869184), by norm_num⟩
  | 6 => ⟨((403508231/68719476736), (134778167/17179869184)), (95/137438953472), by norm_num⟩
  | 7 => ⟨((-51642121/34359738368), (-551977273/274877906944)), (99/549755813888), by norm_num⟩
  | 8 => ⟨((740242075/2199023255552), (494505253/1099511627776)), (91/2199023255552), by norm_num⟩
  | 9 => ⟨((-589482555/8796093022208), (-787586195/8796093022208)), (75/8796093022208), by norm_num⟩
  | 10 => ⟨((105621095/8796093022208), (564466009/35184372088832)), (109/70368744177664), by norm_num⟩
  | 11 => ⟨((-17204327/8796093022208), (-183888603/70368744177664)), (73/281474976710656), by norm_num⟩
  | 12 => ⟨((657621671/2251799813685248), (878624389/2251799813685248)), (89/2251799813685248), by norm_num⟩
  | 13 => ⟨((-181276901/4503599627370496), (-968789889/18014398509481984)), (25/4503599627370496), by norm_num⟩
  | 14 => ⟨((742410523/144115188075855872), (495953845/72057594037927936)), (13/18014398509481984), by norm_num⟩
  | 15 => ⟨((-709451245/1152921504606846976), (-473935999/576460752303423488)), (101/1152921504606846976), by norm_num⟩
  | 16 => ⟨((635582993/9223372036854775808), (424589657/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (1209184220037/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779584187358973/633825300114114700748351602688), (716128263189/316912650057057350374175801344)), (46171/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890659036399911/39614081257132168796771975168), (402766938045/9903520314283042199192993792)), (51947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472622810801699/618970019642690137449562112), (26742023529/38685626227668133590597632)), (55199/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886078639134453/77371252455336267181195264), (1711185844173/154742504910672534362390528)), (55205/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387614844131365/2417851639229258349412352), (400978538887/2417851639229258349412352)), (51761/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259581163135211/604462909807314587353088), (1403102388307/604462909807314587353088)), (45297/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118067462330307/4722366482869645213696), (2279436858167/75557863725914323419136)), (73619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298504593757117/4722366482869645213696), (854524423323/2361183241434822606848)), (55225/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622774575086289/590295810358705651712), (1174541584947/295147905179352825856)), (37975/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825131782095559/73786976294838206464), (366883249663/9223372036854775808)), (94963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456129983964791/2305843009213693952), (103130598435/288230376151711744)), (106867/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595766853870001/1152921504606846976), (1648983905203/576460752303423488)), (106911/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196137346679825/144115188075855872), (2883235838681/144115188075855872)), (93595/144115188075855872), by norm_num⟩
  | 4 => ⟨((373492177758973/9007199254740992), (4319886168183/36028797018963968)), (70245/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492165586118739/9007199254740992), (2695587161273/4503599627370496)), (175783/9007199254740992), by norm_num⟩
  | 2 => ⟨((279218154374659/562949953421312), (10756338021527/4503599627370496)), (352075/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224752953617179/2251799813685248), (16069618687747/2251799813685248)), (264697/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098923081221669/1125899906842624), (31880511893957/2251799813685248)), (1063927/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098923081221669/1125899906842624), (31880511893957/2251799813685248)), (4058559426314543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2144733895694045/2251799813685248), (15558323678913/562949953421312)), (2106997/2251799813685248), by norm_num⟩
  | 2 => ⟨((2041038671570923/2251799813685248), (59274299520851/1125899906842624)), (258131/140737488355328), by norm_num⟩
  | 3 => ⟨((1843762959425121/2251799813685248), (26863208891189/281474976710656)), (7921933/2251799813685248), by norm_num⟩
  | 4 => ⟨((372288578083741/562949953421312), (351927479335315/2251799813685248)), (14484979/2251799813685248), by norm_num⟩
  | 5 => ⟨((464900921145375/1125899906842624), (465471504435085/2251799813685248)), (11842985/1125899906842624), by norm_num⟩
  | 6 => ⟨((8990971085507/70368744177664), (96100075088221/562949953421312)), (29352879/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1444653197/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1568941237/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-785117525382859/4503599627370496), (-300728277226857/4503599627370496)), (73717385/2251799813685248), by norm_num⟩
  | 1 => ⟨((1456993257/4294967296), (279040435/2147483648)), (69/1073741824), by norm_num⟩
  | 2 => ⟨((-1417588983/4294967296), (-542987615/4294967296)), (271/4294967296), by norm_num⟩
  | 3 => ⟨((919500263/4294967296), (44025213/536870912)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((-894632447/8589934592), (-342676435/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((1392699487/34359738368), (266727021/17179869184)), (273/34359738368), by norm_num⟩
  | 6 => ⟨((-451678011/34359738368), (-173008939/34359738368)), (179/68719476736), by norm_num⟩
  | 7 => ⟨((1004485515/274877906944), (384754115/274877906944)), (201/274877906944), by norm_num⟩
  | 8 => ⟨((-977319279/1099511627776), (-374348469/1099511627776)), (197/1099511627776), by norm_num⟩
  | 9 => ⟨((845233557/4398046511104), (161877441/2199023255552)), (43/1099511627776), by norm_num⟩
  | 10 => ⟨((-657899423/17592186044416), (-503998329/35184372088832)), (135/17592186044416), by norm_num⟩
  | 11 => ⟨((116383015/17592186044416), (178315539/70368744177664)), (193/140737488355328), by norm_num⟩
  | 12 => ⟨((-1207844747/1125899906842624), (-462648023/1125899906842624)), (63/281474976710656), by norm_num⟩
  | 13 => ⟨((1446373755/9007199254740992), (554013221/9007199254740992)), (19/562949953421312), by norm_num⟩
  | 14 => ⟨((-804146677/36028797018963968), (-38502141/4503599627370496)), (171/36028797018963968), by norm_num⟩
  | 15 => ⟨((26079953/9007199254740992), (159832975/144115188075855872)), (179/288230376151711744), by norm_num⟩
  | 16 => ⟨((-202996981/576460752303423488), (-4859697/36028797018963968)), (11/144115188075855872), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-3615783430489/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779370365748567/633825300114114700748351602688), (-4281890204419/633825300114114700748351602688)), (92621/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945209009513749/19807040628566084398385987584), (-1204097065499/9903520314283042199192993792)), (52113/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890234561792821/2475880078570760549798248448), (-159891664801/77371252455336267181195264)), (110771/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885949960867253/77371252455336267181195264), (-2557772014073/77371252455336267181195264)), (110807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550217387846669/9671406556917033397649408), (-4794771479813/9671406556917033397649408)), (103919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629684353274651/302231454903657293676544), (-2097187014075/302231454903657293676544)), (45483/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472183203209065/18889465931478580854784), (-3406943601675/37778931862957161709568)), (73945/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298243481661761/4722366482869645213696), (-5108691198487/4722366482869645213696)), (27745/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811206820165981/295147905179352825856), (-7021648687885/590295810358705651712)), (19087/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912338879126411/36893488147419103232), (-2193214627313/18446744073709551616)), (47755/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912002618895499/4611686018427387904), (-2465921985675/2305843009213693952)), (215105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199405907704521/144115188075855872), (-1232058265773/144115188075855872)), (215363/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74729825480927/9007199254740992), (-1077035507545/18014398509481984)), (188733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493267536368907/36028797018963968), (-6454090189059/18014398509481984)), (283681/36028797018963968), by norm_num⟩
  | 3 => ⟨((745634991993677/4503599627370496), (-4026699950599/2251799813685248)), (355621/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115948428609933/2251799813685248), (-16064170147613/2251799813685248)), (11161/70368744177664), by norm_num⟩
  | 1 => ⟨((1110919124788803/1125899906842624), (-23989712948537/1125899906842624)), (134891/281474976710656), by norm_num⟩
  | 0 => ⟨((1095726487019659/1125899906842624), (-23776727531705/562949953421312)), (547259/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095726487019659/1125899906842624), (-23776727531705/562949953421312)), (2087627413036155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1064353230677973/1125899906842624), (-92558103869815/1125899906842624)), (555707/281474976710656), by norm_num⟩
  | 2 => ⟨((998561941634313/1125899906842624), (-87498467919347/562949953421312)), (4568107/1125899906842624), by norm_num⟩
  | 3 => ⟨((858426240071315/1125899906842624), (-155204986668115/562949953421312)), (2380737/281474976710656), by norm_num⟩
  | 4 => ⟨((568914922368769/1125899906842624), (-473335266611587/1125899906842624)), (9886107/562949953421312), by norm_num⟩
  | 5 => ⟨((88478481675125/1125899906842624), (-956701372198877/2251799813685248)), (36606441/1125899906842624), by norm_num⟩
  | 6 => ⟨((-785117525382859/4503599627370496), (-300728277226857/4503599627370496)), (73717385/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1568941237/33554432)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-838302217/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((716085737739689/4503599627370496), (110275874853131/2251799813685248)), (120499561/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1420076781/4294967296), (-218689189/2147483648)), (61/2147483648), by norm_num⟩
  | 2 => ⟨((1476483325/4294967296), (56843923/536870912)), (65/2147483648), by norm_num⟩
  | 3 => ⟨((-511710127/2147483648), (-39401205/536870912)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((1064071295/8589934592), (163865005/4294967296)), (49/4294967296), by norm_num⟩
  | 5 => ⟨((-442534811/8589934592), (-272598159/17179869184)), (83/17179869184), by norm_num⟩
  | 6 => ⟨((613483513/34359738368), (377901291/68719476736)), (59/34359738368), by norm_num⟩
  | 7 => ⟨((-728973201/137438953472), (-224521041/137438953472)), (143/274877906944), by norm_num⟩
  | 8 => ⟨((1515857157/1099511627776), (116719595/274877906944)), (151/1099511627776), by norm_num⟩
  | 9 => ⟨((-700474743/2199023255552), (-107871811/1099511627776)), (71/2199023255552), by norm_num⟩
  | 10 => ⟨((36414907/549755813888), (44862625/2199023255552)), (15/2199023255552), by norm_num⟩
  | 11 => ⟨((-55071033/4398046511104), (-271386781/70368744177664)), (93/70368744177664), by norm_num⟩
  | 12 => ⟨((152689325/70368744177664), (94055491/140737488355328)), (131/562949953421312), by norm_num⟩
  | 13 => ⟨((-781559447/2251799813685248), (-481434819/4503599627370496)), (85/2251799813685248), by norm_num⟩
  | 14 => ⟨((464344909/9007199254740992), (143016509/9007199254740992)), (103/18014398509481984), by norm_num⟩
  | 15 => ⟨((-514974983/72057594037927936), (-9913149/4503599627370496)), (29/36028797018963968), by norm_num⟩
  | 16 => ⟨((1070860373/1152921504606846976), (329821021/1152921504606846976)), (123/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (389189878425/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779202410123049/633825300114114700748351602688), (230399830957/316912650057057350374175801344)), (46123/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890229657341077/39614081257132168796771975168), (518317960845/39614081257132168796771975168)), (103779/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945017589125299/1237940039285380274899124224), (550612085031/2475880078570760549798248448)), (110269/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771701382322399/154742504910672534362390528), (550498778483/154742504910672534362390528)), (110273/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775016076792195/4835703278458516698824704), (257986124669/4835703278458516698824704)), (103385/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259207522498525/604462909807314587353088), (112838849873/151115727451828646838272)), (45233/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472118141885301/18889465931478580854784), (45826687803/4722366482869645213696)), (73507/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649024882775473/2361183241434822606848), (549723002389/4722366482869645213696)), (27567/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811074831965659/295147905179352825856), (377774370751/295147905179352825856)), (151629/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824351359093353/73786976294838206464), (943955602927/73786976294838206464)), (11847/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911821471793623/4611686018427387904), (1061290023977/9223372036854775808)), (53317/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594891089884977/1152921504606846976), (1060465611065/1152921504606846976)), (13331/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195372433339651/144115188075855872), (231745200519/36028797018963968)), (93333/72057594037927936), by norm_num⟩
  | 4 => ⟨((373206024283407/9007199254740992), (1388620128061/36028797018963968)), (140031/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490739632525395/9007199254740992), (1732540588215/9007199254740992)), (350189/9007199254740992), by norm_num⟩
  | 2 => ⟨((278863466451209/562949953421312), (3455396669425/4503599627370496)), (700711/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220532576879251/2251799813685248), (5158950834759/2251799813685248)), (1051911/2251799813685248), by norm_num⟩
  | 0 => ⟨((2189548137700041/2251799813685248), (2555431631945/562949953421312)), (2107227/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189548137700041/2251799813685248), (2555431631945/562949953421312)), (8038433083541106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266121378467849/281474976710656), (19878287711865/2251799813685248)), (1029269/562949953421312), by norm_num⟩
  | 2 => ⟨((2012666695814611/2251799813685248), (37587975949279/2251799813685248)), (3928847/1125899906842624), by norm_num⟩
  | 3 => ⟨((224787653630173/281474976710656), (4199533351967/140737488355328)), (14308799/2251799813685248), by norm_num⟩
  | 4 => ⟨((1434129470199579/2251799813685248), (107320744124345/2251799813685248)), (11854063/1125899906842624), by norm_num⟩
  | 5 => ⟨((886968274511/2199023255552), (273402353045909/4503599627370496)), (64916777/4503599627370496), by norm_num⟩
  | 6 => ⟨((716085737739689/4503599627370496), (110275874853131/2251799813685248)), (120499561/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-838302217/16777216)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile028Terms0

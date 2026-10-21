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
namespace Reinmann.XiBand58.Tile007Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2893/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2893/160))
  have he : value ((15/16), (2893/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-21804525/8388608), (-1682146417/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1326994442147551/18014398509481984), (178365905076225/18014398509481984)), (23619543/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1754383957/8589934592), (-117906403/4294967296)), (1/67108864), by norm_num⟩
  | 2 => ⟨((1216046293/4294967296), (81726491/2147483648)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((-1123865413/4294967296), (-18882829/536870912)), (43/2147483648), by norm_num⟩
  | 4 => ⟨((1558008285/8589934592), (209417275/8589934592)), (121/8589934592), by norm_num⟩
  | 5 => ⟨((-107992905/1073741824), (-116125595/8589934592)), (17/2147483648), by norm_num⟩
  | 6 => ⟨((1596906189/34359738368), (214645677/34359738368)), (1/268435456), by norm_num⟩
  | 7 => ⟨((-158127289/8589934592), (-170035481/68719476736)), (103/68719476736), by norm_num⟩
  | 8 => ⟨((1753687753/274877906944), (235719229/274877906944)), (145/274877906944), by norm_num⟩
  | 9 => ⟨((-540250543/274877906944), (-36308471/137438953472)), (91/549755813888), by norm_num⟩
  | 10 => ⟨((599157025/1099511627776), (40267383/549755813888)), (103/2199023255552), by norm_num⟩
  | 11 => ⟨((-1208157099/8796093022208), (-81196285/4398046511104)), (53/4398046511104), by norm_num⟩
  | 12 => ⟨((1116574249/35184372088832), (150082603/35184372088832)), (25/8796093022208), by norm_num⟩
  | 13 => ⟨((-476277103/70368744177664), (-64018051/70368744177664)), (87/140737488355328), by norm_num⟩
  | 14 => ⟨((754583157/562949953421312), (202852259/1125899906842624)), (35/281474976710656), by norm_num⟩
  | 15 => ⟨((-1115812667/4503599627370496), (-37495059/1125899906842624)), (105/4503599627370496), by norm_num⟩
  | 16 => ⟨((193355601/4503599627370496), (207916755/36028797018963968)), (37/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (43511343655/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888980288135985/316912650057057350374175801344), (803887873/2475880078570760549798248448)), (92221/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118052054142775/2475880078570760549798248448), (115733922301/19807040628566084398385987584)), (51875/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888551426842935/2475880078570760549798248448), (245869414989/2475880078570760549798248448)), (110235/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770218012231891/154742504910672534362390528), (245796135795/154742504910672534362390528)), (55119/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774320949567653/4835703278458516698824704), (57589012263/2417851639229258349412352)), (51675/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257991454710243/604462909807314587353088), (100741874717/302231454903657293676544)), (90433/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886497216156183/75557863725914323419136), (163632651943/37778931862957161709568)), (146957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296568915605359/4722366482869645213696), (245321486387/4722366482869645213696)), (110221/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202514321621757/73786976294838206464), (168555004165/295147905179352825856)), (75779/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821809110887633/73786976294838206464), (421077199039/73786976294838206464)), (189455/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455196283473079/2305843009213693952), (236642781681/4611686018427387904)), (53287/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796018025983957/576460752303423488), (472753294677/1152921504606846976)), (213161/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192877389782373/144115188075855872), (51632642305/18014398509481984)), (186531/144115188075855872), by norm_num⟩
  | 4 => ⟨((46533992249209/1125899906842624), (618397735555/36028797018963968)), (279827/36028797018963968), by norm_num⟩
  | 3 => ⟨((743040033012827/4503599627370496), (770912247675/9007199254740992)), (174919/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221621112172155/4503599627370496), (1535587806989/4503599627370496)), (699839/4503599627370496), by norm_num⟩
  | 1 => ⟨((275835455980231/281474976710656), (1143926538035/1125899906842624)), (1050181/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162172583057539/2251799813685248), (4513968675049/2251799813685248)), (2102111/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2162172583057539/2251799813685248), (4513968675049/2251799813685248)), (8018917092330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038051845150825/1125899906842624), (2167150749959/562949953421312)), (7901/4398046511104), by norm_num⟩
  | 2 => ⟨((1914082842538427/2251799813685248), (15984474790649/2251799813685248)), (3745251/1125899906842624), by norm_num⟩
  | 3 => ⟨((1626902001856957/2251799813685248), (849198737545/70368744177664)), (6420275/1125899906842624), by norm_num⟩
  | 4 => ⟨((1175091880612567/2251799813685248), (39266385729387/2251799813685248)), (18864245/2251799813685248), by norm_num⟩
  | 5 => ⟨((612531838066013/2251799813685248), (81963966372463/4503599627370496)), (20346349/2251799813685248), by norm_num⟩
  | 6 => ⟨((1326994442147551/18014398509481984), (178365905076225/18014398509481984)), (23619543/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-1682146417/33554432)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-89125185/33554432), (-13429123/262144)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722823689500283/18014398509481984), (-519044424757855/9007199254740992)), (160276855/18014398509481984), by norm_num⟩
  | 1 => ⟨((-61032585/536870912), (701219363/4294967296)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((691673337/4294967296), (-248338007/1073741824)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-40826211/268435456), (469063037/2147483648)), (151/4294967296), by norm_num⟩
  | 4 => ⟨((462677463/4294967296), (-166119457/1073741824)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-524345585/8589934592), (188260745/2147483648)), (125/8589934592), by norm_num⟩
  | 6 => ⟨((495194303/17179869184), (-177794285/4294967296)), (15/2147483648), by norm_num⟩
  | 7 => ⟨((-200427301/17179869184), (1151380893/68719476736)), (49/17179869184), by norm_num⟩
  | 8 => ⟨((70981663/17179869184), (-50970433/8589934592)), (141/137438953472), by norm_num⟩
  | 9 => ⟨((-89380531/68719476736), (128364543/68719476736)), (45/137438953472), by norm_num⟩
  | 10 => ⟨((405174581/1099511627776), (-290947309/549755813888)), (103/1099511627776), by norm_num⟩
  | 11 => ⟨((-52179365/549755813888), (599502399/4398046511104)), (215/8796093022208), by norm_num⟩
  | 12 => ⟨((394227395/17592186044416), (-141543183/4398046511104)), (103/17592186044416), by norm_num⟩
  | 13 => ⟨((-687341733/140737488355328), (987131163/140737488355328)), (181/140737488355328), by norm_num⟩
  | 14 => ⟨((278197967/281474976710656), (-399536169/281474976710656)), (37/140737488355328), by norm_num⟩
  | 15 => ⟨((-105092559/562949953421312), (1207435953/4503599627370496)), (113/2251799813685248), by norm_num⟩
  | 16 => ⟨((595499281/18014398509481984), (-427615457/9007199254740992)), (81/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (-1253837090325/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888935942089905/316912650057057350374175801344), (-1482426928141/633825300114114700748351602688)), (92347/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888733046721187/39614081257132168796771975168), (-208418494509/4951760157141521099596496896)), (25975/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888445311870007/2475880078570760549798248448), (-1771077387833/2475880078570760549798248448)), (27601/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770111833583233/154742504910672534362390528), (-1770537855963/154742504910672534362390528)), (110417/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548542289065547/9671406556917033397649408), (-1659306209915/9671406556917033397649408)), (12941/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257904228390091/604462909807314587353088), (-362830038525/151115727451828646838272)), (90601/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886355346970957/75557863725914323419136), (-2357321820703/75557863725914323419136)), (73625/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296462403267787/4722366482869645213696), (-220881580779/590295810358705651712)), (110459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809983969669425/295147905179352825856), (-607043241507/147573952589676412928)), (37979/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113851596914089/4611686018427387904), (-3032931316019/73786976294838206464)), (189947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820578260670899/9223372036854775808), (-3408908833575/9223372036854775808)), (106881/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591828720146673/1152921504606846976), (-1702494725813/576460752303423488)), (53463/288230376151711744), by norm_num⟩
  | 5 => ⟨((596347730154627/72057594037927936), (-92967571493/4503599627370496)), (93611/72057594037927936), by norm_num⟩
  | 4 => ⟨((93050864623971/2251799813685248), (-4453651002671/36028797018963968)), (70259/9007199254740992), by norm_num⟩
  | 3 => ⟨((185716985870587/1125899906842624), (-5551709653407/9007199254740992)), (87913/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220927449371675/4503599627370496), (-2764371834237/1125899906842624)), (704377/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205630031426469/2251799813685248), (-16471856008073/2251799813685248)), (16551/35184372088832), by norm_num⟩
  | 0 => ⟨((1080006846541347/1125899906842624), (-32488931795399/2251799813685248)), (532347/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1080006846541347/1125899906842624), (-32488931795399/2251799813685248)), (2030742647411155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2071500137475161/2251799813685248), (-1947790194459/70368744177664)), (2073315/1125899906842624), by norm_num⟩
  | 2 => ⟨((1903911641515857/2251799813685248), (-14334658457907/281474976710656)), (3929391/1125899906842624), by norm_num⟩
  | 3 => ⟨((1603929728136009/2251799813685248), (-193920777144021/2251799813685248)), (14089753/2251799813685248), by norm_num⟩
  | 4 => ⟨((1125759621074667/2251799813685248), (-138127420330273/1125899906842624)), (175771/17592186044416), by norm_num⟩
  | 5 => ⟨((528918236965567/2251799813685248), (-276220419641201/2251799813685248)), (56032489/4503599627370496), by norm_num⟩
  | 6 => ⟨((722823689500283/18014398509481984), (-519044424757855/9007199254740992)), (160276855/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-13429123/262144)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45461617/16777216), (-1753606101/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-494631967091117/18014398509481984), (-1092165308692547/18014398509481984)), (53513717/4503599627370496), by norm_num⟩
  | 1 => ⟨((170429977/2147483648), (752631131/4294967296)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((-61575749/536870912), (-1087691883/4294967296)), (217/4294967296), by norm_num⟩
  | 3 => ⟨((29662801/268435456), (523972317/2147483648)), (211/4294967296), by norm_num⟩
  | 4 => ⟨((-342946089/4294967296), (-378618697/2147483648)), (77/2147483648), by norm_num⟩
  | 5 => ⟨((99124169/2147483648), (875479031/8589934592)), (45/2147483648), by norm_num⟩
  | 6 => ⟨((-191003799/8589934592), (-421743311/8589934592)), (175/17179869184), by norm_num⟩
  | 7 => ⟨((630939413/68719476736), (348284273/17179869184)), (291/68719476736), by norm_num⟩
  | 8 => ⟨((-455912365/137438953472), (-1006671027/137438953472)), (53/34359738368), by norm_num⟩
  | 9 => ⟨((585669433/549755813888), (161647417/68719476736)), (137/274877906944), by norm_num⟩
  | 10 => ⟨((-169280239/549755813888), (-373776903/549755813888)), (5/34359738368), by norm_num⟩
  | 11 => ⟨((88960513/1099511627776), (785712149/4398046511104)), (85/2199023255552), by norm_num⟩
  | 12 => ⟨((-171419303/8796093022208), (-757000069/17592186044416)), (83/8796093022208), by norm_num⟩
  | 13 => ⟨((609803707/140737488355328), (673234345/70368744177664)), (149/70368744177664), by norm_num⟩
  | 14 => ⟨((-125897101/140737488355328), (-555970725/281474976710656)), (31/70368744177664), by norm_num⟩
  | 15 => ⟨((24259295/140737488355328), (214261611/562949953421312)), (193/2251799813685248), by norm_num⟩
  | 16 => ⟨((-560947049/18014398509481984), (-1238591419/18014398509481984)), (281/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (-1300040233695/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888892735330901/316912650057057350374175801344), (-1536917407173/316912650057057350374175801344)), (92503/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29509931889009/618970019642690137449562112), (-864312215313/9903520314283042199192993792)), (52043/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236042695025503/309485009821345068724781056), (-1836155557319/1237940039285380274899124224)), (55307/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770007792057921/154742504910672534362390528), (-3671168771303/154742504910672534362390528)), (110639/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548444442431161/9671406556917033397649408), (-860126849083/2417851639229258349412352)), (103751/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257818305185873/604462909807314587353088), (-3009231109539/604462909807314587353088)), (90809/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943107573019477/37778931862957161709568), (-1221931855765/18889465931478580854784)), (147615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324089187364237/1180591620717411303424), (-3663807565035/4722366482869645213696)), (27689/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619821849005423/590295810358705651712), (-5034506747085/590295810358705651712)), (152361/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910720857657073/36893488147419103232), (-6288293685597/73786976294838206464)), (5955/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820369768595193/9223372036854775808), (-1766920248733/2305843009213693952)), (419/18014398509481984), by norm_num⟩
  | 6 => ⟨((1591618136538053/1152921504606846976), (-7059377117151/1152921504606846976)), (107357/576460752303423488), by norm_num⟩
  | 5 => ⟨((596254426876613/72057594037927936), (-3083811966913/72057594037927936)), (188085/144115188075855872), by norm_num⟩
  | 4 => ⟨((744264625002743/18014398509481984), (-9232800836959/36028797018963968)), (282547/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485372016857305/9007199254740992), (-11508450423089/9007199254740992)), (2765/70368744177664), by norm_num⟩
  | 2 => ⟨((1110087723356113/2251799813685248), (-11459745804041/2251799813685248)), (177513/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102220960950171/1125899906842624), (-8534140518375/562949953421312)), (267657/562949953421312), by norm_num⟩
  | 0 => ⟨((539350084277099/562949953421312), (-67307497709735/2251799813685248)), (2163561/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((539350084277099/562949953421312), (-67307497709735/2251799813685248)), (8253330239302825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032473199226719/1125899906842624), (-128971693990203/2251799813685248)), (2137531/1125899906842624), by norm_num⟩
  | 2 => ⟨((1886211156436667/2251799813685248), (-236539352556083/2251799813685248)), (8330347/2251799813685248), by norm_num⟩
  | 3 => ⟨((777565048206363/1125899906842624), (-24767030966521/140737488355328)), (1963235/281474976710656), by norm_num⟩
  | 4 => ⟨((125532791167955/281474976710656), (-136836161085877/562949953421312)), (27221333/2251799813685248), by norm_num⟩
  | 5 => ⟨((78710001455117/562949953421312), (-244105894379033/1125899906842624)), (1172307/70368744177664), by norm_num⟩
  | 6 => ⟨((-494631967091117/18014398509481984), (-1092165308692547/18014398509481984)), (53513717/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-1753606101/33554432)), (1/16777216), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-92624041/33554432), (-446602253/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-280915075002557/4503599627370496), (-95249663882473/9007199254740992)), (97519533/9007199254740992), by norm_num⟩
  | 1 => ⟨((197204899/1073741824), (267464469/8589934592)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-1161315583/4294967296), (-98441601/2147483648)), (205/4294967296), by norm_num⟩
  | 3 => ⟨((1139807623/4294967296), (96618429/2147483648)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((-1678046997/8589934592), (-71121767/2147483648)), (301/8589934592), by norm_num⟩
  | 5 => ⟨((988181397/8589934592), (83765481/4294967296)), (179/8589934592), by norm_num⟩
  | 6 => ⟨((-969879941/17179869184), (-20553529/2147483648)), (89/8589934592), by norm_num⟩
  | 7 => ⟨((1631858459/68719476736), (2161379/536870912)), (301/68719476736), by norm_num⟩
  | 8 => ⟨((-600613457/68719476736), (-101824777/68719476736)), (7/4294967296), by norm_num⟩
  | 9 => ⟨((392993261/137438953472), (66625965/137438953472)), (295/549755813888), by norm_num⟩
  | 10 => ⟨((-925715741/1099511627776), (-156940871/1099511627776)), (175/1099511627776), by norm_num⟩
  | 11 => ⟨((495584275/2199023255552), (42009347/1099511627776)), (189/4398046511104), by norm_num⟩
  | 12 => ⟨((-972811771/17592186044416), (-82462639/8796093022208)), (187/17592186044416), by norm_num⟩
  | 13 => ⟨((1762698399/140737488355328), (298838411/140737488355328)), (341/140737488355328), by norm_num⟩
  | 14 => ⟨((-741451125/281474976710656), (-62850819/140737488355328)), (289/562949953421312), by norm_num⟩
  | 15 => ⟨((1164350717/2251799813685248), (197397761/2251799813685248)), (229/2251799813685248), by norm_num⟩
  | 16 => ⟨((-857089909/9007199254740992), (-290612831/18014398509481984)), (339/18014398509481984), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (-1936758716093/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777701236292431/633825300114114700748351602688), (-4578918157393/633825300114114700748351602688)), (92651/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888540562328137/39614081257132168796771975168), (-160938420931/1237940039285380274899124224)), (52131/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888240112678173/2475880078570760549798248448), (-683795357975/309485009821345068724781056)), (27703/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769905865236933/154742504910672534362390528), (-1367156710689/38685626227668133590597632)), (55425/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774174188619085/4835703278458516698824704), (-1281248406281/2417851639229258349412352)), (51981/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257733739852977/604462909807314587353088), (-4482525923753/604462909807314587353088)), (91007/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886076775412623/75557863725914323419136), (-1820162304563/18889465931478580854784)), (147961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648126069801329/2361183241434822606848), (-5457464583337/4722366482869645213696)), (111037/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619676660668241/590295810358705651712), (-7499104674725/590295810358705651712)), (9549/36893488147419103232), by norm_num⟩
  | 8 => ⟨((910629104375793/36893488147419103232), (-4683260466077/36893488147419103232)), (47785/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910080275195037/4611686018427387904), (-10527222314241/9223372036854775808)), (107627/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591405460289567/1152921504606846976), (-164290458811/18014398509481984)), (53883/288230376151711744), by norm_num⟩
  | 5 => ⟨((596159441778811/72057594037927936), (-9186066302487/144115188075855872)), (188903/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488236567255191/36028797018963968), (-6875366189413/18014398509481984)), (283979/36028797018963968), by norm_num⟩
  | 3 => ⟨((371248176650153/2251799813685248), (-535588889507/281474976710656)), (356071/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109688359975229/2251799813685248), (-17064630770529/2251799813685248)), (357719/2251799813685248), by norm_num⟩
  | 1 => ⟨((68848265239097/70368744177664), (-25411912131645/1125899906842624)), (540711/1125899906842624), by norm_num⟩
  | 0 => ⟨((1077206797793327/1125899906842624), (-12521673019943/281474976710656)), (68627/70368744177664), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1077206797793327/1125899906842624), (-12521673019943/281474976710656)), (261791229516482331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2056782848016531/2251799813685248), (-191682137495205/2251799813685248)), (4397565/2251799813685248), by norm_num⟩
  | 2 => ⟨((1862338568718985/2251799813685248), (-175081519358537/1125899906842624)), (4391053/1125899906842624), by norm_num⟩
  | 3 => ⟨((92861573732081/140737488355328), (-579200804955567/2251799813685248)), (4314421/562949953421312), by norm_num⟩
  | 4 => ⟨((207843079169045/562949953421312), (-382168950743719/1125899906842624)), (31651905/2251799813685248), by norm_num⟩
  | 5 => ⟨((95006226250847/4503599627370496), (-564392418918499/2251799813685248)), (89718933/4503599627370496), by norm_num⟩
  | 6 => ⟨((-280915075002557/4503599627370496), (-95249663882473/9007199254740992)), (97519533/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-446602253/8388608)), (1/16777216), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-94237589/33554432), (-1817528965/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-787673903526673/18014398509481984), (747910114923035/18014398509481984)), (199948621/18014398509481984), by norm_num⟩
  | 1 => ⟨((8790419/67108864), (-267092999/2147483648)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((-842679741/4294967296), (800139117/4294967296)), (219/4294967296), by norm_num⟩
  | 3 => ⟨((420740483/2147483648), (-799000859/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-315106461/2147483648), (598398165/4294967296)), (167/4294967296), by norm_num⟩
  | 5 => ⟨((188794919/2147483648), (-358528139/4294967296)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((-23565793/536870912), (716036211/17179869184)), (51/4294967296), by norm_num⟩
  | 7 => ⟨((322728259/17179869184), (-612872225/34359738368)), (11/2147483648), by norm_num⟩
  | 8 => ⟨((-966807461/137438953472), (114750069/17179869184)), (133/68719476736), by norm_num⟩
  | 9 => ⟨((643621403/274877906944), (-611129751/274877906944)), (179/274877906944), by norm_num⟩
  | 10 => ⟨((-192811741/274877906944), (732312447/1099511627776)), (217/1099511627776), by norm_num⟩
  | 11 => ⟨((420081713/2199023255552), (-398874915/2199023255552)), (119/2199023255552), by norm_num⟩
  | 12 => ⟨((-419484115/8796093022208), (796614971/17592186044416)), (15/1099511627776), by norm_num⟩
  | 13 => ⟨((193332631/17592186044416), (-91786353/8796093022208)), (223/70368744177664), by norm_num⟩
  | 14 => ⟨((-330955887/140737488355328), (628496777/281474976710656)), (3/4398046511104), by norm_num⟩
  | 15 => ⟨((1057552247/2251799813685248), (-1004164309/2251799813685248)), (309/2251799813685248), by norm_num⟩
  | 16 => ⟨((-792035849/9007199254740992), (752051857/9007199254740992)), (233/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (3102929850943/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777631223107743/633825300114114700748351602688), (1833854271449/316912650057057350374175801344)), (46281/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944231018858001/19807040628566084398385987584), (2062580775817/19807040628566084398385987584)), (26039/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472039250170153/618970019642690137449562112), (1095431869747/618970019642690137449562112)), (27673/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884911556664115/77371252455336267181195264), (4380314208605/154742504910672534362390528)), (110723/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548271179614989/9671406556917033397649408), (513130432899/1208925819614629174706176)), (103835/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257666573883023/604462909807314587353088), (3590412476485/604462909807314587353088)), (11361/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885968346144295/75557863725914323419136), (2915803955987/37778931862957161709568)), (18469/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648085721465791/2361183241434822606848), (1092811573187/1180591620717411303424)), (110867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809783358735017/295147905179352825856), (6006468939531/590295810358705651712)), (9533/36893488147419103232), by norm_num⟩
  | 8 => ⟨((227640287433743/9223372036854775808), (3751048980355/36893488147419103232)), (190789/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455002434552275/2305843009213693952), (8431632675341/9223372036854775808)), (214815/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591257249542727/1152921504606846976), (1052669706669/144115188075855872)), (215037/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149024014731009/18014398509481984), (3678570726593/72057594037927936)), (188409/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488052236310389/36028797018963968), (2753162859715/9007199254740992)), (283113/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484772429358355/9007199254740992), (13725530501843/9007199254740992)), (354769/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109483198808649/2251799813685248), (13665249671717/2251799813685248)), (178045/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202603966328183/2251799813685248), (40695357703045/2251799813685248)), (537447/1125899906842624), by norm_num⟩
  | 0 => ⟨((538407176860461/562949953421312), (80195217426525/2251799813685248)), (2176413/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((538407176860461/562949953421312), (80195217426525/2251799813685248)), (8302356728560637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2056881481413493/2251799813685248), (76698968265145/1125899906842624)), (4318079/2251799813685248), by norm_num⟩
  | 2 => ⟨((934192834567419/1125899906842624), (280239276172441/2251799813685248)), (8476919/2251799813685248), by norm_num⟩
  | 3 => ⟨((189422419789519/281474976710656), (465045821877393/2251799813685248)), (8088517/1125899906842624), by norm_num⟩
  | 4 => ⟨((461876533278683/1125899906842624), (39119865077551/140737488355328)), (28454933/2251799813685248), by norm_num⟩
  | 5 => ⟨((409935715586739/4503599627370496), (1027078023091069/4503599627370496)), (78329845/4503599627370496), by norm_num⟩
  | 6 => ⟨((-787673903526673/18014398509481984), (747910114923035/18014398509481984)), (199948621/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1817528965/33554432)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-95772395/33554432), (-923565127/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73505660811683/18014398509481984), (1035015143875805/18014398509481984)), (330612449/36028797018963968), by norm_num⟩
  | 1 => ⟨((-106711213/8589934592), (-751287181/4294967296)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((81221171/4294967296), (285913835/1073741824)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-82426559/4294967296), (-1160628115/4294967296)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((62737377/4294967296), (1766779169/8589934592)), (291/8589934592), by norm_num⟩
  | 5 => ⟨((-76402141/8589934592), (-1075799765/8589934592)), (179/8589934592), by norm_num⟩
  | 6 => ⟨((77536011/17179869184), (272941377/4294967296)), (183/17179869184), by norm_num⟩
  | 7 => ⟨((-33722875/17179869184), (-1899374049/68719476736)), (321/68719476736), by norm_num⟩
  | 8 => ⟨((51335025/68719476736), (90354483/8589934592)), (123/68719476736), by norm_num⟩
  | 9 => ⟨((-138925009/549755813888), (-1956168895/549755813888)), (335/549755813888), by norm_num⟩
  | 10 => ⟨((84592061/1099511627776), (1191120019/1099511627776)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((-5853237/274877906944), (-1318687863/4398046511104)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((95041661/17592186044416), (1338258263/17592186044416)), (235/17592186044416), by norm_num⟩
  | 13 => ⟨((-11129095/8796093022208), (-1253648403/70368744177664)), (111/35184372088832), by norm_num⟩
  | 14 => ⟨((77446353/281474976710656), (1090503055/281474976710656)), (97/140737488355328), by norm_num⟩
  | 15 => ⟨((-1964893/35184372088832), (-1770699211/2251799813685248)), (317/2251799813685248), by norm_num⟩
  | 16 => ⟨((95714573/9007199254740992), (673866685/4503599627370496)), (243/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (1953782581111/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777565154821213/633825300114114700748351602688), (2309225088531/633825300114114700748351602688)), (23107/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59012123966717/1237940039285380274899124224), (2597238838381/39614081257132168796771975168)), (25999/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944039321909389/1237940039285380274899124224), (2758762941281/2475880078570760549798248448)), (110513/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769745142284947/154742504910672534362390528), (689464909841/38685626227668133590597632)), (27633/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387049622839167/2417851639229258349412352), (1292267017055/4835703278458516698824704)), (25911/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628801690435967/302231454903657293676544), (2260508330193/604462909807314587353088)), (90709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942933211986377/37778931862957161709568), (3671528915335/75557863725914323419136)), (9215/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648047835579785/2361183241434822606848), (2752075114323/4722366482869645213696)), (110613/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202432952286357/73786976294838206464), (3781551180577/590295810358705651712)), (152147/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113812190835481/4611686018427387904), (147597306307/2305843009213693952)), (190265/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454967205095983/2305843009213693952), (5308248249271/9223372036854775808)), (13385/576460752303423488), by norm_num⟩
  | 6 => ⟨((795559558925305/576460752303423488), (5301687024917/1152921504606846976)), (214301/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596037189104245/72057594037927936), (18092205955/562949953421312)), (187671/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487881856054547/36028797018963968), (6932689097559/36028797018963968)), (281823/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484570305811593/9007199254740992), (4320080363635/4503599627370496)), (352833/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109297254550973/2251799813685248), (17203442424085/4503599627370496)), (353667/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101063172032191/1125899906842624), (12806872118721/1125899906842624)), (1065187/2251799813685248), by norm_num⟩
  | 0 => ⟨((2152990210539957/2251799813685248), (50466464095895/2251799813685248)), (1073607/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2152990210539957/2251799813685248), (50466464095895/2251799813685248)), (4095485691550826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2057385365487073/2251799813685248), (48251981592097/1125899906842624)), (4202233/2251799813685248), by norm_num⟩
  | 2 => ⟨((117226271112717/140737488355328), (176344131800711/2251799813685248)), (1004879/281474976710656), by norm_num⟩
  | 3 => ⟨((774237207404097/1125899906842624), (73442283378735/562949953421312)), (7325611/1125899906842624), by norm_num⟩
  | 4 => ⟨((128312511144505/281474976710656), (404027022600901/2251799813685248)), (23972931/2251799813685248), by norm_num⟩
  | 5 => ⟨((49430714968191/281474976710656), (368357588628209/2251799813685248)), (60918255/4503599627370496), by norm_num⟩
  | 6 => ⟨((73505660811683/18014398509481984), (1035015143875805/18014398509481984)), (330612449/36028797018963968), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-923565127/16777216)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile007Terms2

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
namespace Reinmann.XiBand58.Tile007Terms1
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

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-69118709/33554432), (-166633687/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-127081378911561/2251799813685248), (-1029458841429013/9007199254740992)), (1592455/70368744177664), by norm_num⟩
  | 1 => ⟨((532581957/4294967296), (269645723/1073741824)), (27/536870912), by norm_num⟩
  | 2 => ⟨((-585101083/4294967296), (-296236105/1073741824)), (15/268435456), by norm_num⟩
  | 3 => ⟨((428532827/4294967296), (867863001/4294967296)), (89/2147483648), by norm_num⟩
  | 4 => ⟨((-235395715/4294967296), (-476722479/4294967296)), (197/8589934592), by norm_num⟩
  | 5 => ⟨((51721725/2147483648), (418986539/8589934592)), (175/17179869184), by norm_num⟩
  | 6 => ⟨((-303051321/34359738368), (-1227476695/68719476736)), (129/34359738368), by norm_num⟩
  | 7 => ⟨((190249089/68719476736), (385291709/68719476736)), (41/34359738368), by norm_num⟩
  | 8 => ⟨((-209009987/274877906944), (-846572413/549755813888)), (91/274877906944), by norm_num⟩
  | 9 => ⟨((408215005/2199023255552), (206678857/549755813888)), (45/549755813888), by norm_num⟩
  | 10 => ⟨((-358776017/8796093022208), (-726591783/8796093022208)), (5/274877906944), by norm_num⟩
  | 11 => ⟨((286658721/35184372088832), (1161080235/70368744177664)), (129/35184372088832), by norm_num⟩
  | 12 => ⟨((-419902391/281474976710656), (-212596169/70368744177664)), (191/281474976710656), by norm_num⟩
  | 13 => ⟨((35485379/140737488355328), (1149837607/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | 14 => ⟨((-89107825/2251799813685248), (-90230409/1125899906842624)), (83/4503599627370496), by norm_num⟩
  | 15 => ⟨((417685127/72057594037927936), (422947141/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | 16 => ⟨((-458874013/576460752303423488), (-929309853/576460752303423488)), (109/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-1321795890965/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889393270155587/316912650057057350374175801344), (-3128629441133/633825300114114700748351602688)), (23127/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889761592383653/39614081257132168796771975168), (-879766273205/9903520314283042199192993792)), (26023/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889537579039109/2475880078570760549798248448), (-934554999113/618970019642690137449562112)), (27655/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771203468195423/154742504910672534362390528), (-467166896313/19342813113834066795298816)), (55323/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387391256185953/2417851639229258349412352), (-3502811796255/9671406556917033397649408)), (51879/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629399225349545/302231454903657293676544), (-1532010311065/302231454903657293676544)), (1419/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((471951800024367/18889465931478580854784), (-1244318013881/18889465931478580854784)), (73813/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324387548254885/1180591620717411303424), (-233213328089/295147905179352825856)), (110765/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101341366502067/36893488147419103232), (-2564095166497/295147905179352825856)), (152375/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823490279684489/73786976294838206464), (-3203242583963/36893488147419103232)), (95289/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822672404330841/9223372036854775808), (-7202138350969/9223372036854775808)), (214551/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796959137128799/576460752303423488), (-449730960693/72057594037927936)), (53685/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194518665313607/144115188075855872), (-6288990389145/144115188075855872)), (94055/72057594037927936), by norm_num⟩
  | 4 => ⟨((372884588194615/9007199254740992), (-9419012691227/36028797018963968)), (141295/18014398509481984), by norm_num⟩
  | 3 => ⟨((93070223583283/562949953421312), (-11748468064047/9007199254740992)), (5531/140737488355328), by norm_num⟩
  | 2 => ⟨((556912285962567/1125899906842624), (-5855290440655/1125899906842624)), (11097/70368744177664), by norm_num⟩
  | 1 => ⟨((2215579014315741/2251799813685248), (-8735680822651/562949953421312)), (1070927/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179381351589067/2251799813685248), (-17282967007219/562949953421312)), (2164391/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2179381351589067/2251799813685248), (-17282967007219/562949953421312)), (8256496438033293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2107169487997951/2251799813685248), (-16727142335987/281474976710656)), (4322465/2251799813685248), by norm_num⟩
  | 2 => ⟨((1963876272511791/2251799813685248), (-250444457718335/2251799813685248)), (4301709/1125899906842624), by norm_num⟩
  | 3 => ⟨((210614169845079/281474976710656), (-436843386437787/2251799813685248)), (8460223/1125899906842624), by norm_num⟩
  | 4 => ⟨((1175993028404143/2251799813685248), (-653737737273073/2251799813685248)), (31886557/2251799813685248), by norm_num⟩
  | 5 => ⟨((848731372933491/4503599627370496), (-1365647189000599/4503599627370496)), (25909859/1125899906842624), by norm_num⟩
  | 6 => ⟨((-127081378911561/2251799813685248), (-1029458841429013/9007199254740992)), (1592455/70368744177664), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-166633687/4194304)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-9054133/4194304), (-1396992361/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-364969707300117/4503599627370496), (46312017825197/562949953421312)), (23681903/1125899906842624), by norm_num⟩
  | 1 => ⟨((200360729/1073741824), (-406789253/2147483648)), (211/4294967296), by norm_num⟩
  | 2 => ⟨((-115336907/536870912), (468333435/2147483648)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((708194781/4294967296), (-718918391/4294967296)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((-815339373/8589934592), (827685385/8589934592)), (221/8589934592), by norm_num⟩
  | 5 => ⟨((750955315/17179869184), (-190581603/4294967296)), (103/8589934592), by norm_num⟩
  | 6 => ⟨((-576379505/34359738368), (73138393/4294967296)), (5/1073741824), by norm_num⟩
  | 7 => ⟨((758378775/137438953472), (-769862279/137438953472)), (213/137438953472), by norm_num⟩
  | 8 => ⟨((-873115831/549755813888), (13849011/8589934592)), (31/68719476736), by norm_num⟩
  | 9 => ⟨((446760777/1099511627776), (-453525707/1099511627776)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-205740941/2199023255552), (417712613/4398046511104)), (119/4398046511104), by norm_num⟩
  | 11 => ⟨((172267645/8796093022208), (-21859519/1099511627776)), (201/35184372088832), by norm_num⟩
  | 12 => ⟨((-528881215/140737488355328), (1073779255/281474976710656)), (39/35184372088832), by norm_num⟩
  | 13 => ⟨((749411693/1125899906842624), (-760759417/1125899906842624)), (223/1125899906842624), by norm_num⟩
  | 14 => ⟨((-493024055/4503599627370496), (1000979025/9007199254740992)), (37/1125899906842624), by norm_num⟩
  | 15 => ⟨((302727957/18014398509481984), (-614623835/36028797018963968)), (23/4503599627370496), by norm_num⟩
  | 16 => ⟨((-697056881/288230376151711744), (11056435/4503599627370496)), (107/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (3059418497583/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778632501522781/633825300114114700748351602688), (905040117587/158456325028528675187087900672)), (92557/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889588231880307/39614081257132168796771975168), (4071899035239/39614081257132168796771975168)), (104149/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472338323061121/618970019642690137449562112), (540679810669/309485009821345068724781056)), (110685/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885509539428523/77371252455336267181195264), (4324365138649/154742504910672534362390528)), (110715/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193674006361073/1208925819614629174706176), (4052952116461/9671406556917033397649408)), (103827/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629323494920129/302231454903657293676544), (443149144897/75557863725914323419136)), (355/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1887560872567013/75557863725914323419136), (2879401019997/37778931862957161709568)), (147739/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297365269435275/4722366482869645213696), (4317232340813/4722366482869645213696)), (110857/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621207305415331/590295810358705651712), (741644758223/73786976294838206464)), (152513/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911585824588947/36893488147419103232), (3705947390043/36893488147419103232)), (11923/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455578337996703/2305843009213693952), (8332124453687/9223372036854775808)), (53697/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199194810322329/144115188075855872), (130067302827/18014398509481984)), (215007/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194203018513909/144115188075855872), (1818745198949/36028797018963968)), (94189/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491063231085373/36028797018963968), (10894909984653/36028797018963968)), (141529/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488526800076303/9007199254740992), (13587939390013/9007199254740992)), (354687/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113223511835765/2251799813685248), (13541960338593/2251799813685248)), (22249/140737488355328), by norm_num⟩
  | 1 => ⟨((138359664273745/140737488355328), (20198231330577/1125899906842624)), (134307/281474976710656), by norm_num⟩
  | 0 => ⟨((1087824501465349/1125899906842624), (4992382234579/140737488355328)), (1087507/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1087824501465349/1125899906842624), (4992382234579/140737488355328)), (4148509983543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049619962185011/1125899906842624), (38588408667233/562949953421312)), (2178615/1125899906842624), by norm_num⟩
  | 2 => ⟨((1946435552972379/2251799813685248), (35974036235303/281474976710656)), (8721403/2251799813685248), by norm_num⟩
  | 3 => ⟨((822850001416047/1125899906842624), (497530145880705/2251799813685248)), (4326673/562949953421312), by norm_num⟩
  | 4 => ⟨((1092811287356045/2251799813685248), (363613744662729/1125899906842624)), (16472257/1125899906842624), by norm_num⟩
  | 5 => ⟨((590973215734685/4503599627370496), (1411710586315099/4503599627370496)), (106510879/4503599627370496), by norm_num⟩
  | 6 => ⟨((-364969707300117/4503599627370496), (46312017825197/562949953421312)), (23681903/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-1396992361/33554432)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-75431263/33554432), (-727408813/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((771213292206109/9007199254740992), (139208183243861/2251799813685248)), (98111693/9007199254740992), by norm_num⟩
  | 1 => ⟨((-220452393/1073741824), (-636685647/4294967296)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((528621751/2147483648), (47709547/268435456)), (139/4294967296), by norm_num⟩
  | 3 => ⟨((-845053065/4294967296), (-152536663/1073741824)), (113/4294967296), by norm_num⟩
  | 4 => ⟨((1013174375/8589934592), (365766943/4294967296)), (69/4294967296), by norm_num⟩
  | 5 => ⟨((-485897209/8589934592), (-701656659/17179869184)), (135/17179869184), by norm_num⟩
  | 6 => ⟨((776753747/34359738368), (280416531/17179869184)), (55/17179869184), by norm_num⟩
  | 7 => ⟨((-1064328079/137438953472), (-384233985/68719476736)), (153/137438953472), by norm_num⟩
  | 8 => ⟨((638036817/274877906944), (115169107/68719476736)), (47/137438953472), by norm_num⟩
  | 9 => ⟨((-679975763/1099511627776), (-490957257/1099511627776)), (51/549755813888), by norm_num⟩
  | 10 => ⟨((652204267/4398046511104), (235452817/2199023255552)), (25/1099511627776), by norm_num⟩
  | 11 => ⟨((-568697283/17592186044416), (-821223559/35184372088832)), (177/35184372088832), by norm_num⟩
  | 12 => ⟨((227279421/35184372088832), (656402697/140737488355328)), (9/8796093022208), by norm_num⟩
  | 13 => ⟨((-670759691/562949953421312), (-242151527/281474976710656)), (27/140737488355328), by norm_num⟩
  | 14 => ⟨((919092281/4503599627370496), (331802287/2251799813685248)), (75/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1175406419/36028797018963968), (-848668945/36028797018963968)), (195/36028797018963968), by norm_num⟩
  | 16 => ⟨((352312687/72057594037927936), (508754813/144115188075855872)), (119/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (814592422539/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444625326465835/158456325028528675187087900672), (963751889243/633825300114114700748351602688)), (92295/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944720516416075/19807040628566084398385987584), (1084008811127/39614081257132168796771975168)), (51919/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889197409116849/2475880078570760549798248448), (287873828139/618970019642690137449562112)), (110335/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442715943901815/38685626227668133590597632), (1151198376671/154742504910672534362390528)), (110343/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549247069819289/9671406556917033397649408), (1078933089389/9671406556917033397649408)), (103455/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629260373345025/302231454903657293676544), (943751183349/604462909807314587353088)), (22633/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887356880169431/75557863725914323419136), (383251198609/18889465931478580854784)), (73565/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81075830176893/295147905179352825856), (1149236829507/4722366482869645213696)), (55181/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202624994947139/73786976294838206464), (394840342059/147573952589676412928)), (75885/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822914917421733/73786976294838206464), (246617953613/9223372036854775808)), (94873/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822027893265207/9223372036854775808), (2217833063681/9223372036854775808)), (213511/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796638611004389/576460752303423488), (2215674428033/1152921504606846976)), (106785/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193961628165655/144115188075855872), (1936289424375/144115188075855872)), (186939/144115188075855872), by norm_num⟩
  | 4 => ⟨((745355272612469/18014398509481984), (1449794820137/18014398509481984)), (280541/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488102334573811/9007199254740992), (452003086619/1125899906842624)), (87727/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112823519151683/2251799813685248), (7206724243671/4503599627370496)), (351257/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212676212294767/2251799813685248), (167921714849/35184372088832)), (1055525/2251799813685248), by norm_num⟩
  | 0 => ⟨((543493406039341/562949953421312), (2655360797085/281474976710656)), (2118115/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((543493406039341/562949953421312), (2655360797085/281474976710656)), (8079967507369231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2098636845775511/2251799813685248), (41017389204145/2251799813685248)), (4129783/2251799813685248), by norm_num⟩
  | 2 => ⟨((1955144572564943/2251799813685248), (38227467547595/1125899906842624)), (7848219/2251799813685248), by norm_num⟩
  | 3 => ⟨((1694975245727257/2251799813685248), (33191327774499/562949953421312)), (14161507/2251799813685248), by norm_num⟩
  | 4 => ⟨((317003585137113/562949953421312), (99935133858145/1125899906842624)), (22989221/2251799813685248), by norm_num⟩
  | 5 => ⟨((696292909516469/2251799813685248), (450196974301623/4503599627370496)), (59944093/4503599627370496), by norm_num⟩
  | 6 => ⟨((771213292206109/9007199254740992), (139208183243861/2251799813685248)), (98111693/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-727408813/16777216)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-19542101/8388608), (-376901989/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((511450382980575/9007199254740992), (-712070128495853/9007199254740992)), (27416619/2251799813685248), by norm_num⟩
  | 1 => ⟨((-606015423/4294967296), (421864461/2147483648)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((752945877/4294967296), (-262073451/1073741824)), (83/2147483648), by norm_num⟩
  | 3 => ⟨((-623666739/4294967296), (868304081/4294967296)), (35/1073741824), by norm_num⟩
  | 4 => ⟨((774876813/8589934592), (-269706823/2147483648)), (11/536870912), by norm_num⟩
  | 5 => ⟨((-385099309/8589934592), (268078511/4294967296)), (177/17179869184), by norm_num⟩
  | 6 => ⟨((318978611/17179869184), (-888200099/34359738368)), (149/34359738368), by norm_num⟩
  | 7 => ⟨((-113233153/17179869184), (630598381/68719476736)), (27/17179869184), by norm_num⟩
  | 8 => ⟨((281373815/137438953472), (-783489055/274877906944)), (17/34359738368), by norm_num⟩
  | 9 => ⟨((-310750073/549755813888), (216321907/274877906944)), (19/137438953472), by norm_num⟩
  | 10 => ⟨((308873969/2199023255552), (-107507949/549755813888)), (153/4398046511104), by norm_num⟩
  | 11 => ⟨((-279099265/8796093022208), (777155541/17592186044416)), (35/4398046511104), by norm_num⟩
  | 12 => ⟨((57794635/8796093022208), (-643719657/70368744177664)), (59/35184372088832), by norm_num⟩
  | 13 => ⟨((-44189007/35184372088832), (984358927/562949953421312)), (183/562949953421312), by norm_num⟩
  | 14 => ⟨((250984131/1125899906842624), (-87358573/281474976710656)), (33/562949953421312), by norm_num⟩
  | 15 => ⟨((-332625139/9007199254740992), (926199035/18014398509481984)), (177/18014398509481984), by norm_num⟩
  | 16 => ⟨((206635605/36028797018963968), (-575379535/72057594037927936)), (223/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (-308693296061/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889187476879021/316912650057057350374175801344), (-1460674938359/633825300114114700748351602688)), (11543/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889298878986045/39614081257132168796771975168), (-1642926281089/39614081257132168796771975168)), (12987/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472261589586961/618970019642690137449562112), (-1745194412275/2475880078570760549798248448)), (110401/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885356355514929/77371252455336267181195264), (-872363996421/77371252455336267181195264)), (110413/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549105432133341/9671406556917033397649408), (-204398386183/1208925819614629174706176)), (103525/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258396799100385/604462909807314587353088), (-1430293487167/604462909807314587353088)), (45299/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887155437998173/75557863725914323419136), (-1161649392575/37778931862957161709568)), (36811/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648531088672525/2361183241434822606848), (-1741662372335/4722366482869645213696)), (55227/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620792150887497/590295810358705651712), (-2393467469447/590295810358705651712)), (151909/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911327549399061/36893488147419103232), (-2989858204217/73786976294838206464)), (189937/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455433879557865/2305843009213693952), (-3360875418471/9223372036854775808)), (106875/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99561546789467/72057594037927936), (-839371192705/288230376151711744)), (106919/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193705604022767/144115188075855872), (-2933989062647/144115188075855872)), (187209/144115188075855872), by norm_num⟩
  | 4 => ⟨((2910793536871/70368744177664), (-2196687137271/18014398509481984)), (70253/9007199254740992), by norm_num⟩
  | 3 => ⟨((371905409704543/2251799813685248), (-1369606508405/2251799813685248)), (2747/70368744177664), by norm_num⟩
  | 2 => ⟨((2224684528911743/4503599627370496), (-2729268615349/1125899906842624)), (176071/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211229707805861/2251799813685248), (-8138254635703/1125899906842624)), (264767/562949953421312), by norm_num⟩
  | 0 => ⟨((2171069977381423/2251799813685248), (-8039663037171/562949953421312)), (532191/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2171069977381423/2251799813685248), (-8039663037171/562949953421312)), (2030147554637718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1046387569431973/1125899906842624), (-62011448592135/2251799813685248)), (2082847/1125899906842624), by norm_num⟩
  | 2 => ⟨((1943273258793405/2251799813685248), (-115264258527645/2251799813685248)), (1993113/562949953421312), by norm_num⟩
  | 3 => ⟨((417779711830725/562949953421312), (-198943040966723/2251799813685248)), (14576423/2251799813685248), by norm_num⟩
  | 4 => ⟨((1222604181596023/2251799813685248), (-295281546150525/2251799813685248)), (24210691/2251799813685248), by norm_num⟩
  | 5 => ⟨((1250173114683261/4503599627370496), (-320643470061351/2251799813685248)), (32639725/2251799813685248), by norm_num⟩
  | 6 => ⟨((511450382980575/9007199254740992), (-712070128495853/9007199254740992)), (27416619/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-376901989/8388608)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-40343165/16777216), (-778085177/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-597098400792315/9007199254740992), (-276126103852891/4503599627370496)), (148765915/9007199254740992), by norm_num⟩
  | 1 => ⟨((730289059/4294967296), (168859833/1073741824)), (23/536870912), by norm_num⟩
  | 2 => ⟨((-468288613/2147483648), (-54139615/268435456)), (239/4294967296), by norm_num⟩
  | 3 => ⟨((400378859/2147483648), (740615311/4294967296)), (207/4294967296), by norm_num⟩
  | 4 => ⟨((-1026951497/8589934592), (-949820383/8589934592)), (67/2147483648), by norm_num⟩
  | 5 => ⟨((1053631433/17179869184), (974496473/17179869184)), (277/17179869184), by norm_num⟩
  | 6 => ⟨((-900837089/34359738368), (-416589017/17179869184)), (239/34359738368), by norm_num⟩
  | 7 => ⟨((660171861/68719476736), (305294209/34359738368)), (177/68719476736), by norm_num⟩
  | 8 => ⟨((-846653695/274877906944), (-783064185/274877906944)), (115/137438953472), by norm_num⟩
  | 9 => ⟨((241291539/274877906944), (446337773/549755813888)), (33/137438953472), by norm_num⟩
  | 10 => ⟨((-990240925/4398046511104), (-915867027/4398046511104)), (273/4398046511104), by norm_num⟩
  | 11 => ⟨((461803241/8796093022208), (106779661/2199023255552)), (257/17592186044416), by norm_num⟩
  | 12 => ⟨((-789667951/70368744177664), (-730358461/70368744177664)), (221/70368744177664), by norm_num⟩
  | 13 => ⟨((155804485/70368744177664), (576409989/281474976710656)), (177/281474976710656), by norm_num⟩
  | 14 => ⟨((-913441403/2251799813685248), (-844835675/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | 15 => ⟨((39048849/562949953421312), (577856193/9007199254740992)), (45/2251799813685248), by norm_num⟩
  | 16 => ⟨((-801266561/72057594037927936), (-46317871/4503599627370496)), (233/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (-3120006867083/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778253175048707/633825300114114700748351602688), (-1845177423647/316912650057057350374175801344)), (23141/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118072597721849/2475880078570760549798248448), (-259422994781/2475880078570760549798248448)), (104157/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944450021263179/1237940039285380274899124224), (-4409107677979/2475880078570760549798248448)), (55347/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770565925247703/154742504910672534362390528), (-275493081951/9671406556917033397649408)), (110725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387241830378835/2417851639229258349412352), (-1032775508835/2417851639229258349412352)), (103837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629137726898359/302231454903657293676544), (-3613420447491/604462909807314587353088)), (45445/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235869664761295/9444732965739290427392), (-733672881941/9444732965739290427392)), (36939/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324228192817559/1180591620717411303424), (-549989504061/590295810358705651712)), (110871/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810292696513803/295147905179352825856), (-3023219467413/295147905179352825856)), (152533/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822394667732141/73786976294838206464), (-7552882767217/73786976294838206464)), (47699/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455359952634931/2305843009213693952), (-8489894083085/9223372036854775808)), (26853/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592685644855131/1152921504606846976), (-265032075681/36028797018963968)), (215047/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193440077706403/144115188075855872), (-7410930423433/144115188075855872)), (188417/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489920405544389/36028797018963968), (-11096481301321/36028797018963968)), (35391/4503599627370496), by norm_num⟩
  | 3 => ⟨((743550522951109/4503599627370496), (-432368716225/281474976710656)), (354793/9007199254740992), by norm_num⟩
  | 2 => ⟨((555900964941133/1125899906842624), (-27567379209809/4503599627370496)), (356117/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209510782177279/2251799813685248), (-41091185407625/2251799813685248)), (67187/140737488355328), by norm_num⟩
  | 0 => ⟨((2167245135772515/2251799813685248), (-40573407810479/1125899906842624)), (2176659/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2167245135772515/2251799813685248), (-40573407810479/1125899906842624)), (8303295144087981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041470614825225/1125899906842624), (-19524941823107/281474976710656)), (4346731/2251799813685248), by norm_num⟩
  | 2 => ⟨((957955020102919/1125899906842624), (-72243200452739/562949953421312)), (8644591/2251799813685248), by norm_num⟩
  | 3 => ⟨((1593039478986507/2251799813685248), (-245868166864237/1125899906842624)), (16928957/2251799813685248), by norm_num⟩
  | 4 => ⟨((509807787030443/1125899906842624), (-173939838728275/562949953421312)), (31346553/2251799813685248), by norm_num⟩
  | 5 => ⟨((493414055318923/4503599627370496), (-1260160107939527/4503599627370496)), (95516647/4503599627370496), by norm_num⟩
  | 6 => ⟨((-597098400792315/9007199254740992), (-276126103852891/4503599627370496)), (148765915/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-778085177/16777216)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83017565/33554432), (-800566055/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-157240337618989/2251799813685248), (848760687389071/18014398509481984)), (276469231/18014398509481984), by norm_num⟩
  | 1 => ⟨((791485339/4294967296), (-267020239/2147483648)), (11/268435456), by norm_num⟩
  | 2 => ⟨((-130548449/536870912), (704681719/4294967296)), (235/4294967296), by norm_num⟩
  | 3 => ⟨((459366455/2147483648), (-619898485/4294967296)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((-606147205/4294967296), (204493455/2147483648)), (139/4294967296), by norm_num⟩
  | 5 => ⟨((1279725779/17179869184), (-431735961/8589934592)), (37/2147483648), by norm_num⟩
  | 6 => ⟨((-1125756565/34359738368), (23736999/1073741824)), (263/34359738368), by norm_num⟩
  | 7 => ⟨((424419445/34359738368), (-286369377/34359738368)), (201/68719476736), by norm_num⟩
  | 8 => ⟨((-1120067247/274877906944), (755745203/274877906944)), (267/274877906944), by norm_num⟩
  | 9 => ⟨((164217871/137438953472), (-110803051/137438953472)), (79/274877906944), by norm_num⟩
  | 10 => ⟨((-346704301/1099511627776), (233932483/1099511627776)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((665434565/8796093022208), (-112247497/2199023255552)), (41/2199023255552), by norm_num⟩
  | 12 => ⟨((-292686661/17592186044416), (197485053/17592186044416)), (291/70368744177664), by norm_num⟩
  | 13 => ⟨((950666927/281474976710656), (-320722693/140737488355328)), (239/281474976710656), by norm_num⟩
  | 14 => ⟨((-716818435/1125899906842624), (60457541/140737488355328)), (91/562949953421312), by norm_num⟩
  | 15 => ⟨((504459985/4503599627370496), (-340375289/4503599627370496)), (129/4503599627370496), by norm_num⟩
  | 16 => ⟨((-332824705/18014398509481984), (449134951/36028797018963968)), (43/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (829772456359/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889072587902715/316912650057057350374175801344), (981345117109/158456325028528675187087900672)), (92587/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472260009548751/9903520314283042199192993792), (275943011557/2475880078570760549798248448)), (104185/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472192720835843/618970019642690137449562112), (4689845532691/2475880078570760549798248448)), (110725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770436722843031/154742504910672534362390528), (1172127985839/38685626227668133590597632)), (55379/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548846148401241/9671406556917033397649408), (4394063357519/9671406556917033397649408)), (51935/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629084690766705/302231454903657293676544), (1921694620465/302231454903657293676544)), (90921/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886784864960387/75557863725914323419136), (6242852981381/75557863725914323419136)), (73905/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648391678292293/2361183241434822606848), (4679817851887/4722366482869645213696)), (110915/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810203663252993/295147905179352825856), (1607744512151/147573952589676412928)), (152599/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822171903081865/73786976294838206464), (4016534025649/36893488147419103232)), (95443/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910594475775755/4611686018427387904), (9029431055373/9223372036854775808)), (214937/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12440894344723/9007199254740992), (9019724600193/1152921504606846976)), (215175/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193219958258917/144115188075855872), (7881348438901/144115188075855872)), (188545/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489589536878227/36028797018963968), (11800224427651/36028797018963968)), (283353/36028797018963968), by norm_num⟩
  | 3 => ⟨((371671565675955/2251799813685248), (1839023157019/1125899906842624)), (355129/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111385369078857/2251799813685248), (14311665629/2199023255552)), (356539/2251799813685248), by norm_num⟩
  | 1 => ⟨((276031542541415/281474976710656), (5460120192453/281474976710656)), (538343/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164693981757125/2251799813685248), (43114180443269/1125899906842624)), (1090883/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2164693981757125/2251799813685248), (43114180443269/1125899906842624)), (4161388401511764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((519413923475913/562949953421312), (165785619781529/2251799813685248)), (4361833/2251799813685248), by norm_num⟩
  | 2 => ⟨((952386683002775/1125899906842624), (305929003824481/2251799813685248)), (8691285/2251799813685248), by norm_num⟩
  | 3 => ⟨((392415990864489/562949953421312), (517564141210053/2251799813685248)), (17065323/2251799813685248), by norm_num⟩
  | 4 => ⟨((121900951439271/281474976710656), (180389432554825/562949953421312)), (31636225/2251799813685248), by norm_num⟩
  | 5 => ⟨((382258071876809/4503599627370496), (1249966513684249/4503599627370496)), (95353505/4503599627370496), by norm_num⟩
  | 6 => ⟨((-157240337618989/2251799813685248), (848760687389071/18014398509481984)), (276469231/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-800566055/16777216)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-85187893/33554432), (-205373813/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((189873838250543/9007199254740992), (1370813508348479/18014398509481984)), (104977241/9007199254740992), by norm_num⟩
  | 1 => ⟨((-122591945/2147483648), (-442532515/2147483648)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((331985141/4294967296), (599200133/2147483648)), (187/4294967296), by norm_num⟩
  | 3 => ⟨((-74919369/1073741824), (-1081776027/4294967296)), (85/2147483648), by norm_num⟩
  | 4 => ⟨((405770825/8589934592), (732375947/4294967296)), (233/8589934592), by norm_num⟩
  | 5 => ⟨((-219769553/8589934592), (-198331083/2147483648)), (255/17179869184), by norm_num⟩
  | 6 => ⟨((396764655/34359738368), (1432241411/34359738368)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((-76747043/17179869184), (-1108166183/68719476736)), (181/68719476736), by norm_num⟩
  | 8 => ⟨((207834845/137438953472), (1500484827/274877906944)), (247/274877906944), by norm_num⟩
  | 9 => ⟨((-250145419/549755813888), (-225743791/137438953472)), (151/549755813888), by norm_num⟩
  | 10 => ⟨((270962541/2199023255552), (489060415/1099511627776)), (165/2199023255552), by norm_num⟩
  | 11 => ⟨((-133414575/4398046511104), (-963200113/8796093022208)), (41/2199023255552), by norm_num⟩
  | 12 => ⟨((60215561/8796093022208), (869464753/35184372088832)), (75/17592186044416), by norm_num⟩
  | 13 => ⟨((-401395107/281474976710656), (-724478215/140737488355328)), (63/70368744177664), by norm_num⟩
  | 14 => ⟨((155285443/562949953421312), (17517173/17592186044416)), (197/1125899906842624), by norm_num⟩
  | 15 => ⟨((-448555493/9007199254740992), (-404799009/2251799813685248)), (287/9007199254740992), by norm_num⟩
  | 16 => ⟨((151838849/18014398509481984), (548108019/18014398509481984)), (49/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (1694111292079/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778051643939823/633825300114114700748351602688), (1001678379719/316912650057057350374175801344)), (46199/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944467588477611/19807040628566084398385987584), (281659979655/4951760157141521099596496896)), (12995/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118041246666147/154742504910672534362390528), (1196744923599/1237940039285380274899124224)), (13809/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770326323826523/154742504910672534362390528), (1196396332065/77371252455336267181195264)), (110489/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774371610089623/4835703278458516698824704), (1121251314089/4835703278458516698824704)), (103601/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258079889726211/604462909807314587353088), (1961449600635/604462909807314587353088)), (90669/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886640509253491/75557863725914323419136), (3185968355383/75557863725914323419136)), (147369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296676023728983/4722366482869645213696), (597065763453/1180591620717411303424)), (27639/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810130629796113/295147905179352825856), (3281891403715/590295810358705651712)), (152061/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455497897455799/18446744073709551616), (4099410867431/73786976294838206464)), (95073/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820989215619707/9223372036854775808), (575972457075/1152921504606846976)), (53503/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592238627867313/1152921504606846976), (143834771817/36028797018963968)), (107067/576460752303423488), by norm_num⟩
  | 5 => ⟨((596526476888881/72057594037927936), (1005420038803/36028797018963968)), (11719/9007199254740992), by norm_num⟩
  | 4 => ⟨((186168466057937/4503599627370496), (11760059537/70368744177664)), (281529/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486399163186919/9007199254740992), (7506579599599/9007199254740992)), (352391/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111120889295319/2251799813685248), (1869217205589/562949953421312)), (706225/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207571149985059/2251799813685248), (22282590197173/2251799813685248)), (1062959/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081887760416505/1125899906842624), (21988165572085/1125899906842624)), (2140481/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1081887760416505/1125899906842624), (21988165572085/1125899906842624)), (8165287026412200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519583330455571/562949953421312), (42257268273805/1125899906842624)), (2098611/1125899906842624), by norm_num⟩
  | 2 => ⟨((957528876124101/1125899906842624), (78003993258087/1125899906842624)), (8062843/2251799813685248), by norm_num⟩
  | 3 => ⟨((1617864821041473/2251799813685248), (132678003690515/1125899906842624)), (14831407/2251799813685248), by norm_num⟩
  | 4 => ⟨((141390941649797/281474976710656), (381304010049801/2251799813685248)), (6201887/562949953421312), by norm_num⟩
  | 5 => ⟨((503622365268523/2251799813685248), (766148858641955/4503599627370496)), (33324205/2251799813685248), by norm_num⟩
  | 6 => ⟨((189873838250543/9007199254740992), (1370813508348479/18014398509481984)), (104977241/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-205373813/4194304)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile007Terms1

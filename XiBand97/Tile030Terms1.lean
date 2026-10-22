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
namespace Reinmann.XiBand97.Tile030Terms1
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
  | 0 => ⟨((-15897303/8388608), (-906405467/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1102695432081719/9007199254740992), (392697873877621/4503599627370496)), (244765103/9007199254740992), by norm_num⟩
  | 1 => ⟨((577657105/2147483648), (-205718379/1073741824)), (259/4294967296), by norm_num⟩
  | 2 => ⟨((-317310597/1073741824), (226004739/1073741824)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((929603523/4294967296), (-331055445/2147483648)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((-510636927/4294967296), (90925395/1073741824)), (239/8589934592), by norm_num⟩
  | 5 => ⟨((897587205/17179869184), (-79913405/2147483648)), (53/4294967296), by norm_num⟩
  | 6 => ⟨((-657400223/34359738368), (117058465/8589934592)), (157/34359738368), by norm_num⟩
  | 7 => ⟨((825403387/137438953472), (-587894255/137438953472)), (199/137438953472), by norm_num⟩
  | 8 => ⟨((-28337447/17179869184), (645867853/549755813888)), (221/549755813888), by norm_num⟩
  | 9 => ⟨((221382169/549755813888), (-630718543/2199023255552)), (109/1099511627776), by norm_num⟩
  | 10 => ⟨((-778282149/8796093022208), (277166057/4398046511104)), (97/4398046511104), by norm_num⟩
  | 11 => ⟨((1243680485/70368744177664), (-885812469/70368744177664)), (313/70368744177664), by norm_num⟩
  | 12 => ⟨((-56930111/17592186044416), (648776309/281474976710656)), (29/35184372088832), by norm_num⟩
  | 13 => ⟨((1231638047/2251799813685248), (-27413601/70368744177664)), (317/2251799813685248), by norm_num⟩
  | 14 => ⟨((-773195825/9007199254740992), (550709375/9007199254740992)), (201/9007199254740992), by norm_num⟩
  | 15 => ⟨((906071931/72057594037927936), (-645350493/72057594037927936)), (119/36028797018963968), by norm_num⟩
  | 16 => ⟨((-497710879/288230376151711744), (354494991/288230376151711744)), (33/72057594037927936), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (102690244869/316912650057057350374175801344)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889518881768749/316912650057057350374175801344), (1945033123781/316912650057057350374175801344)), (92583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945022001957583/19807040628566084398385987584), (4375578158693/39614081257132168796771975168)), (26045/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889837369724799/2475880078570760549798248448), (4648150858671/2475880078570760549798248448)), (865/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((221437869188407/19342813113834066795298816), (1161784338543/38685626227668133590597632)), (3461/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774922733954801/4835703278458516698824704), (4355614551039/9671406556917033397649408)), (12983/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((39345109822463/18889465931478580854784), (3810086159687/604462909807314587353088)), (90915/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944102410522733/37778931862957161709568), (3094685873315/37778931862957161709568)), (147801/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297847877573501/4722366482869645213696), (1160065785185/1180591620717411303424)), (110907/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621870317816495/590295810358705651712), (6377493189233/590295810358705651712)), (38147/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911999777168457/36893488147419103232), (7967564564293/73786976294838206464)), (190871/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823243562874505/9223372036854775808), (8957596653923/9223372036854775808)), (214917/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594487216279209/1152921504606846976), (8950207299485/1152921504606846976)), (13447/72057594037927936), by norm_num⟩
  | 5 => ⟨((597506999906935/72057594037927936), (3911560900903/72057594037927936)), (188523/144115188075855872), by norm_num⟩
  | 4 => ⟨((746138192266773/18014398509481984), (5859036072535/18014398509481984)), (17707/2251799813685248), by norm_num⟩
  | 3 => ⟨((1490037440991163/9007199254740992), (14618541129875/9007199254740992)), (177533/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114725464411667/2251799813685248), (7287503257431/1125899906842624)), (356459/2251799813685248), by norm_num⟩
  | 1 => ⟨((138638570986671/140737488355328), (21753810110433/1125899906842624)), (538175/1125899906842624), by norm_num⟩
  | 0 => ⟨((546100291861479/562949953421312), (43073646870503/1125899906842624)), (272587/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546100291861479/562949953421312), (43073646870503/1125899906842624)), (1039836884618663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1057862043323295/1125899906842624), (83568818096751/1125899906842624)), (1099427/562949953421312), by norm_num⟩
  | 2 => ⟨((987732878018165/1125899906842624), (78518774300155/562949953421312)), (1114593/281474976710656), by norm_num⟩
  | 3 => ⟨((1689236211617477/2251799813685248), (275532751878241/1125899906842624)), (18132385/2251799813685248), by norm_num⟩
  | 4 => ⟨((1132359001769503/2251799813685248), (206696838293813/562949953421312)), (9019899/562949953421312), by norm_num⟩
  | 5 => ⟨((531716521050895/4503599627370496), (831530490612289/2251799813685248)), (125562157/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1102695432081719/9007199254740992), (392697873877621/4503599627370496)), (244765103/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-906405467/16777216)), (1/16777216), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-949869093/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1233350790665641/9007199254740992), (-41962814031889/4503599627370496)), (40619803/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1354167531/4294967296), (46073413/2147483648)), (91/4294967296), by norm_num⟩
  | 2 => ⟨((1559042985/4294967296), (-53043977/2147483648)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((-74788107/268435456), (40712757/2147483648)), (21/1073741824), by norm_num⟩
  | 4 => ⟨((1377647843/8589934592), (-93744587/8589934592)), (99/8589934592), by norm_num⟩
  | 5 => ⟨((-1268860555/17179869184), (86341955/17179869184)), (93/17179869184), by norm_num⟩
  | 6 => ⟨((1947772933/68719476736), (-132539799/68719476736)), (145/68719476736), by norm_num⟩
  | 7 => ⟨((-320350923/34359738368), (21798869/34359738368)), (49/68719476736), by norm_num⟩
  | 8 => ⟨((184408815/68719476736), (-50193751/274877906944)), (115/549755813888), by norm_num⟩
  | 9 => ⟨((-377437323/549755813888), (51366837/1099511627776)), (15/274877906944), by norm_num⟩
  | 10 => ⟨((695265243/4398046511104), (-94621211/8796093022208)), (113/8796093022208), by norm_num⟩
  | 11 => ⟨((-145537035/4398046511104), (79226687/35184372088832)), (97/35184372088832), by norm_num⟩
  | 12 => ⟨((1787260839/281474976710656), (-121617459/281474976710656)), (151/281474976710656), by norm_num⟩
  | 13 => ⟨((-1266252359/1125899906842624), (21541119/281474976710656)), (109/1125899906842624), by norm_num⟩
  | 14 => ⟨((1666087889/9007199254740992), (-56686011/4503599627370496)), (73/4503599627370496), by norm_num⟩
  | 15 => ⟨((-511507885/18014398509481984), (34806497/18014398509481984)), (91/36028797018963968), by norm_num⟩
  | 16 => ⟨((1177790431/288230376151711744), (-80144921/288230376151711744)), (107/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-88502179845/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889452867045311/316912650057057350374175801344), (-52376525213/316912650057057350374175801344)), (92211/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236236994780151/4951760157141521099596496896), (-117826724507/39614081257132168796771975168)), (51869/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118105043702675/154742504910672534362390528), (-125165538579/2475880078570760549798248448)), (55111/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885673494551973/77371252455336267181195264), (-62568511533/77371252455336267181195264)), (110223/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387425000266119/2417851639229258349412352), (-29321417647/2417851639229258349412352)), (103335/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314729245033397/151115727451828646838272), (-102594683575/604462909807314587353088)), (90419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888000606923089/75557863725914323419136), (-166659611185/75557863725914323419136)), (146933/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297695944402867/4722366482869645213696), (-124945074437/4722366482869645213696)), (55101/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810831701180751/295147905179352825856), (-21464857919/73786976294838206464)), (151529/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823743895668819/73786976294838206464), (-214527730201/73786976294838206464)), (189415/73786976294838206464), by norm_num⟩
  | 7 => ⟨((14241875365101/72057594037927936), (-241177646049/9223372036854775808)), (213097/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797104408427401/576460752303423488), (-120485129139/576460752303423488)), (213105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597388072743329/72057594037927936), (-26326988189/18014398509481984)), (93237/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491931065568751/36028797018963968), (-157729159263/18014398509481984)), (279727/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489625789215867/9007199254740992), (-393509554501/9007199254740992)), (174843/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228687366544081/4503599627370496), (-392292236149/2251799813685248)), (699457/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108610137098225/1125899906842624), (-1170808954879/2251799813685248)), (1049403/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182996159256109/2251799813685248), (-1158729795707/1125899906842624)), (2099717/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182996159256109/2251799813685248), (-1158729795707/1125899906842624)), (8009784707076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116292412738459/2251799813685248), (-561662426267/281474976710656)), (4075443/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988930525376089/2251799813685248), (-8445808896547/2251799813685248)), (1919163/562949953421312), by norm_num⟩
  | 3 => ⟨((439179060128235/562949953421312), (-7459867002273/1125899906842624)), (6809293/1125899906842624), by norm_num⟩
  | 4 => ⟨((342595879578761/562949953421312), (-11639462296173/1125899906842624)), (21429239/2251799813685248), by norm_num⟩
  | 5 => ⟨((1667474228863013/4503599627370496), (-3541728531059/281474976710656)), (26525561/2251799813685248), by norm_num⟩
  | 6 => ⟨((1233350790665641/9007199254740992), (-41962814031889/4503599627370496)), (40619803/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-949869093/16777216)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1978373451/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-424192754934311/4503599627370496), (-379722223508875/4503599627370496)), (310716249/9007199254740992), by norm_num⟩
  | 1 => ⟨((970048715/4294967296), (868353009/4294967296)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((-581518807/2147483648), (-260277447/1073741824)), (27/268435456), by norm_num⟩
  | 3 => ⟨((232403533/1073741824), (832157413/4294967296)), (347/4294967296), by norm_num⟩
  | 4 => ⟨((-557279333/4294967296), (-997713163/8589934592)), (419/8589934592), by norm_num⟩
  | 5 => ⟨((1069037983/17179869184), (956964671/17179869184)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((-854480375/34359738368), (-382450177/17179869184)), (325/34359738368), by norm_num⟩
  | 7 => ⟨((292707779/34359738368), (524043127/68719476736)), (225/68719476736), by norm_num⟩
  | 8 => ⟨((-87735325/34359738368), (-157075067/68719476736)), (17/17179869184), by norm_num⟩
  | 9 => ⟨((23375569/34359738368), (669599219/1099511627776)), (73/274877906944), by norm_num⟩
  | 10 => ⟨((-358733865/2199023255552), (-642251521/4398046511104)), (141/2199023255552), by norm_num⟩
  | 11 => ⟨((312802269/8796093022208), (140004717/4398046511104)), (31/2199023255552), by norm_num⟩
  | 12 => ⟨((-1000089443/140737488355328), (-447622199/70368744177664)), (399/140737488355328), by norm_num⟩
  | 13 => ⟨((368939961/281474976710656), (165130947/140737488355328)), (297/562949953421312), by norm_num⟩
  | 14 => ⟨((-505531079/2251799813685248), (-452533391/2251799813685248)), (409/4503599627370496), by norm_num⟩
  | 15 => ⟨((80814039/2251799813685248), (289367381/9007199254740992)), (263/18014398509481984), by norm_num⟩
  | 16 => ⟨((-96891801/18014398509481984), (-693872675/144115188075855872)), (317/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-3141190192429/10141204801825835211973625643008)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778771607651079/633825300114114700748351602688), (-3717474756999/633825300114114700748351602688)), (138849/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472436168514273/9903520314283042199192993792), (-2090693542555/19807040628566084398385987584)), (156241/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472379861995929/618970019642690137449562112), (-4441784710969/2475880078570760549798248448)), (83023/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771185162523005/154742504910672534362390528), (-4440728389621/154742504910672534362390528)), (41523/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387386919441461/2417851639229258349412352), (-2081030360007/4835703278458516698824704)), (9735/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258783086818795/604462909807314587353088), (-3640681205169/604462909807314587353088)), (136339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943890943344997/37778931862957161709568), (-5914003817823/75557863725914323419136)), (110821/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297530904537389/4722366482869645213696), (-2216831542003/2361183241434822606848)), (20789/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621434849841143/590295810358705651712), (-6093297978055/590295810358705651712)), (228809/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823455774094101/73786976294838206464), (-7612140867745/73786976294838206464)), (286207/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822632572528565/9223372036854775808), (-2139374692835/2305843009213693952)), (80563/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593877178484123/1152921504606846976), (-8549802894829/1152921504606846976)), (80647/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194481287697123/144115188075855872), (-7472424837599/144115188075855872)), (70661/36028797018963968), by norm_num⟩
  | 4 => ⟨((745739728298893/18014398509481984), (-11191344789293/36028797018963968)), (106181/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489045022724737/9007199254740992), (-13958948273141/9007199254740992)), (532235/9007199254740992), by norm_num⟩
  | 2 => ⟨((69608665691601/140737488355328), (-3478414368709/562949953421312)), (66779/281474976710656), by norm_num⟩
  | 1 => ⟨((1107642333590093/1125899906842624), (-1297341465883/70368744177664)), (806353/1125899906842624), by norm_num⟩
  | 0 => ⟨((544661948730827/562949953421312), (-41064063569085/1125899906842624)), (1632797/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544661948730827/562949953421312), (-41064063569085/1125899906842624)), (6228626255515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052438399774973/1125899906842624), (-39730055487909/562949953421312)), (819653/281474976710656), by norm_num⟩
  | 2 => ⟨((978162152240551/1125899906842624), (-148551166108269/1125899906842624)), (6592161/1125899906842624), by norm_num⟩
  | 3 => ⟨((207552585590185/281474976710656), (-516234622545781/2251799813685248)), (26387695/2251799813685248), by norm_num⟩
  | 4 => ⟨((553001792077615/1125899906842624), (-761316916570465/2251799813685248)), (51014231/2251799813685248), by norm_num⟩
  | 5 => ⟨((571667585010131/4503599627370496), (-747863316523605/2251799813685248)), (169215613/4503599627370496), by norm_num⟩
  | 6 => ⟨((-424192754934311/4503599627370496), (-379722223508875/4503599627370496)), (310716249/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1978373451/33554432)), (3/33554432), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1025080911/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-42456817394143/2251799813685248), (1042579930155597/9007199254740992)), (88813441/4503599627370496), by norm_num⟩
  | 1 => ⟨((201227623/4294967296), (-617674303/2147483648)), (213/4294967296), by norm_num⟩
  | 2 => ⟨((-250015929/4294967296), (1534862983/4294967296)), (267/4294967296), by norm_num⟩
  | 3 => ⟨((51772187/1073741824), (-1271330411/4294967296)), (223/4294967296), by norm_num⟩
  | 4 => ⟨((-257298103/8589934592), (197446087/1073741824)), (35/1073741824), by norm_num⟩
  | 5 => ⟨((255744707/17179869184), (-785016151/8589934592)), (281/17179869184), by norm_num⟩
  | 6 => ⟨((-52958477/8589934592), (325115309/8589934592)), (235/34359738368), by norm_num⟩
  | 7 => ⟨((300792849/137438953472), (-115411599/8589934592)), (21/8589934592), by norm_num⟩
  | 8 => ⟨((-93430269/137438953472), (1147148199/274877906944)), (211/274877906944), by norm_num⟩
  | 9 => ⟨((103184665/549755813888), (-1266913861/1099511627776)), (235/1099511627776), by norm_num⟩
  | 10 => ⟨((-12820213/274877906944), (1259265071/4398046511104)), (235/4398046511104), by norm_num⟩
  | 11 => ⟨((185350007/17592186044416), (-1137874963/17592186044416)), (107/8796093022208), by norm_num⟩
  | 12 => ⟨((-76762911/35184372088832), (471252177/35184372088832)), (179/70368744177664), by norm_num⟩
  | 13 => ⟨((234767591/562949953421312), (-1441252515/562949953421312)), (69/140737488355328), by norm_num⟩
  | 14 => ⟨((-20834841/281474976710656), (1023250845/2251799813685248)), (197/2251799813685248), by norm_num⟩
  | 15 => ⟨((3451509/281474976710656), (-1356097509/18014398509481984)), (263/18014398509481984), by norm_num⟩
  | 16 => ⟨((-274453685/144115188075855872), (1684887859/144115188075855872)), (329/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (564118609987/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778659502757973/633825300114114700748351602688), (1335058897743/316912650057057350374175801344)), (92463/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889618782843131/39614081257132168796771975168), (3003315366811/39614081257132168796771975168)), (52019/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944692990705535/1237940039285380274899124224), (398790550925/309485009821345068724781056)), (3455/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771052025174601/154742504910672534362390528), (797384793603/38685626227668133590597632)), (55291/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549423211098745/9671406556917033397649408), (2989358880535/9671406556917033397649408)), (51847/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157334315981629/75557863725914323419136), (2614855166299/604462909807314587353088)), (22689/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887606132948919/75557863725914323419136), (33184192823/590295810358705651712)), (73761/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648699830750593/2361183241434822606848), (1592157715083/2361183241434822606848)), (13835/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405313829923229/147573952589676412928), (4376213170925/590295810358705651712)), (152247/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911616376677167/36893488147419103232), (1366734331569/18446744073709551616)), (95201/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455595896383085/2305843009213693952), (6145729658801/9223372036854775808)), (214331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593630576777261/1152921504606846976), (3070007605803/576460752303423488)), (53623/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194268189323061/144115188075855872), (2683045092135/72057594037927936)), (93931/72057594037927936), by norm_num⟩
  | 4 => ⟨((186395643995283/4503599627370496), (1004537885619/4503599627370496)), (70539/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488661462134781/9007199254740992), (5011477067835/4503599627370496)), (353333/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113369011050883/2251799813685248), (9989380230903/2251799813685248)), (354289/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214244932784717/2251799813685248), (29800712923135/2251799813685248)), (66729/140737488355328), by norm_num⟩
  | 0 => ⟨((2176842572507911/2251799813685248), (29467180732869/1125899906842624)), (2154583/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176842572507911/2251799813685248), (29467180732869/1125899906842624)), (8219081887252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2102838048810389/2251799813685248), (113945144006589/2251799813685248)), (4278505/2251799813685248), by norm_num⟩
  | 2 => ⟨((1957964618740427/2251799813685248), (212814818473669/2251799813685248)), (8423945/2251799813685248), by norm_num⟩
  | 3 => ⟨((420589707647841/562949953421312), (92522408604603/562949953421312)), (16241699/2251799813685248), by norm_num⟩
  | 4 => ⟨((74755893069289/140737488355328), (553000813651523/2251799813685248)), (29607651/2251799813685248), by norm_num⟩
  | 5 => ⟨((124881399503509/562949953421312), (1174955448634679/4503599627370496)), (45995739/2251799813685248), by norm_num⟩
  | 6 => ⟨((-42456817394143/2251799813685248), (1042579930155597/9007199254740992)), (88813441/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1025080911/16777216)), (1/16777216), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-529050181/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((958565526409239/9007199254740992), (-230358017517867/9007199254740992)), (37846419/2251799813685248), by norm_num⟩
  | 1 => ⟨((-146548273/536870912), (281742405/4294967296)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((1503555595/4294967296), (-90331875/1073741824)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((-1285514653/4294967296), (308928913/4294967296)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((206079999/1073741824), (-396193509/8589934592)), (17/536870912), by norm_num⟩
  | 5 => ⟨((-422867809/4294967296), (406486515/17179869184)), (141/8589934592), by norm_num⟩
  | 6 => ⟨((723089677/17179869184), (-347539109/34359738368)), (61/8589934592), by norm_num⟩
  | 7 => ⟨((-132477743/8589934592), (127345745/34359738368)), (181/68719476736), by norm_num⟩
  | 8 => ⟨((1359194807/274877906944), (-326635387/274877906944)), (117/137438953472), by norm_num⟩
  | 9 => ⟨((-48420359/34359738368), (372356989/1099511627776)), (269/1099511627776), by norm_num⟩
  | 10 => ⟨((99356615/274877906944), (-47753841/549755813888)), (139/2199023255552), by norm_num⟩
  | 11 => ⟨((-741366359/8796093022208), (89080861/4398046511104)), (131/8796093022208), by norm_num⟩
  | 12 => ⟨((316927861/17592186044416), (-152325265/35184372088832)), (113/35184372088832), by norm_num⟩
  | 13 => ⟨((-250124281/70368744177664), (240434825/281474976710656)), (45/70368744177664), by norm_num⟩
  | 14 => ⟨((1466413975/2251799813685248), (-44050225/281474976710656)), (133/1125899906842624), by norm_num⟩
  | 15 => ⟨((-250751839/2251799813685248), (30129759/1125899906842624)), (23/1125899906842624), by norm_num⟩
  | 16 => ⟨((1286331537/72057594037927936), (-38640653/9007199254740992)), (119/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-307212024383/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889278420991551/316912650057057350374175801344), (-363486865701/633825300114114700748351602688)), (23059/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889503522801137/39614081257132168796771975168), (-204422022971/19807040628566084398385987584)), (12971/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889263821062003/2475880078570760549798248448), (-434298803281/2475880078570760549798248448)), (6891/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((885465102961565/77371252455336267181195264), (-434188603303/154742504910672534362390528)), (110259/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549309367739583/9671406556917033397649408), (-406934767563/9671406556917033397649408)), (103371/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629287638423633/302231454903657293676544), (-355950917971/604462909807314587353088)), (90453/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943722764073527/37778931862957161709568), (-18068779817/2361183241434822606848)), (9187/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1297279800679519/4722366482869645213696), (-108364733307/1180591620717411303424)), (220499/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621091473313825/590295810358705651712), (-148923640851/147573952589676412928)), (303203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455757346744845/18446744073709551616), (-372075654201/36893488147419103232)), (379029/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822156777673969/9223372036854775808), (-209132185403/2305843009213693952)), (106611/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593406238738033/1152921504606846976), (-835727642713/1152921504606846976)), (426489/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597037333074779/72057594037927936), (-730361483389/144115188075855872)), (373229/144115188075855872), by norm_num⟩
  | 4 => ⟨((93180024850513/2251799813685248), (-34179512331/1125899906842624)), (69993/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488315164133815/9007199254740992), (-1364040080379/9007199254740992)), (350055/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113037114087335/2251799813685248), (-2718682040111/4503599627370496)), (1400763/4503599627370496), by norm_num⟩
  | 1 => ⟨((138332548995311/140737488355328), (-1013652118359/562949953421312)), (2102517/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087638837848703/1125899906842624), (-250501290933/70368744177664)), (4210609/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087638837848703/1125899906842624), (-250501290933/70368744177664)), (16062198647505950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32833241052835/35184372088832), (-241988591787/35184372088832)), (4082511/1125899906842624), by norm_num⟩
  | 2 => ⟨((1960803564643383/2251799813685248), (-451636297281/35184372088832)), (7675567/1125899906842624), by norm_num⟩
  | 3 => ⟨((213380154440445/281474976710656), (-25169414971939/1125899906842624)), (13564385/1125899906842624), by norm_num⟩
  | 4 => ⟨((646473048865933/1125899906842624), (-76321578801071/2251799813685248)), (10586101/562949953421312), by norm_num⟩
  | 5 => ⟨((739801388260629/2251799813685248), (-21911292221417/562949953421312)), (102994635/4503599627370496), by norm_num⟩
  | 6 => ⟨((958565526409239/9007199254740992), (-230358017517867/9007199254740992)), (37846419/2251799813685248), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-529050181/8388608)), (1/8388608), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1088671597/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-432982996218479/9007199254740992), (-204298562904315/2251799813685248)), (330717733/9007199254740992), by norm_num⟩
  | 1 => ⟨((544866061/4294967296), (514178867/2147483648)), (209/2147483648), by norm_num⟩
  | 2 => ⟨((-359483193/2147483648), (-1356947507/4294967296)), (277/2147483648), by norm_num⟩
  | 3 => ⟨((632464503/4294967296), (1193687421/4294967296)), (245/2147483648), by norm_num⟩
  | 4 => ⟨((-26079845/268435456), (-6152753/33554432)), (325/4294967296), by norm_num⟩
  | 5 => ⟨((440487719/8589934592), (207839589/2147483648)), (345/8589934592), by norm_num⟩
  | 6 => ⟨((-387490781/17179869184), (-731334121/17179869184)), (305/17179869184), by norm_num⟩
  | 7 => ⟨((73043599/8589934592), (1102875813/68719476736)), (231/34359738368), by norm_num⟩
  | 8 => ⟨((-385532491/137438953472), (-181909531/34359738368)), (307/137438953472), by norm_num⟩
  | 9 => ⟨((226098299/274877906944), (853457211/549755813888)), (181/274877906944), by norm_num⟩
  | 10 => ⟨((-238674549/1099511627776), (-900929003/2199023255552)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((28630719/549755813888), (432291507/4398046511104)), (185/4398046511104), by norm_num⟩
  | 12 => ⟨((-100744145/8796093022208), (-190140345/8796093022208)), (327/35184372088832), by norm_num⟩
  | 13 => ⟨((654448183/281474976710656), (1235178513/281474976710656)), (533/281474976710656), by norm_num⟩
  | 14 => ⟨((-246732325/562949953421312), (-931344831/1125899906842624)), (101/281474976710656), by norm_num⟩
  | 15 => ⟨((347275067/4503599627370496), (1310865281/9007199254740992)), (571/9007199254740992), by norm_num⟩
  | 16 => ⟨((-458239405/36028797018963968), (-864862157/36028797018963968)), (379/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-335101853121/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222306627247681/79228162514264337593543950336), (-1585774783085/316912650057057350374175801344)), (2891/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889386445558699/39614081257132168796771975168), (-891819323449/9903520314283042199192993792)), (208193/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944569531549257/1237940039285380274899124224), (-473668896863/309485009821345068724781056)), (221251/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221350629941793/19342813113834066795298816), (-1894180176135/77371252455336267181195264)), (221303/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774595795306391/4835703278458516698824704), (-887633837259/2417851639229258349412352)), (207527/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39327243393063/18889465931478580854784), (-3105666250309/604462909807314587353088)), (90821/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887276548055157/75557863725914323419136), (-2522367729437/37778931862957161709568)), (36909/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297152356164333/4722366482869645213696), (-1890913280365/2361183241434822606848)), (110773/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405228771415719/147573952589676412928), (-2598604770487/295147905179352825856)), (152387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822807177712977/73786976294838206464), (-3246155527279/36893488147419103232)), (190595/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821904424778285/9223372036854775808), (-1824519286757/2305843009213693952)), (429145/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593150932489359/1152921504606846976), (-7290866272901/1152921504606846976)), (429529/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298461989719659/36028797018963968), (-6371402783189/144115188075855872)), (376269/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490533728607335/36028797018963968), (-596306957945/2251799813685248)), (565267/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487870309774231/9007199254740992), (-11897841177033/9007199254740992)), (354049/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225150148880553/4503599627370496), (-23710946332239/4503599627370496)), (710373/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211849379530961/2251799813685248), (-35355131804349/2251799813685248)), (535631/562949953421312), by norm_num⟩
  | 0 => ⟨((542999388476319/562949953421312), (-69868423996505/2251799813685248)), (2165421/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((542999388476319/562949953421312), (-69868423996505/2251799813685248)), (8260425571921920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046427783868153/1125899906842624), (-67392334386629/1125899906842624)), (4311737/1125899906842624), by norm_num⟩
  | 2 => ⟨((242132842690953/281474976710656), (-125270835699179/1125899906842624)), (8530953/1125899906842624), by norm_num⟩
  | 3 => ⟨((1638440909837971/2251799813685248), (-431046253682347/2251799813685248)), (33150995/2251799813685248), by norm_num⟩
  | 4 => ⟨((1109640265103225/2251799813685248), (-627270516476089/2251799813685248)), (30466989/1125899906842624), by norm_num⟩
  | 5 => ⟨((372072691367265/2251799813685248), (-309105906290503/1125899906842624)), (47001019/1125899906842624), by norm_num⟩
  | 6 => ⟨((-432982996218479/9007199254740992), (-204298562904315/2251799813685248)), (330717733/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1088671597/16777216)), (1/8388608), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1117132737/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-356401444758109/4503599627370496), (501225779557665/9007199254740992)), (79296521/2251799813685248), by norm_num⟩
  | 1 => ⟨((920441631/4294967296), (-647232329/4294967296)), (103/1073741824), by norm_num⟩
  | 2 => ⟨((-77893817/268435456), (876368819/4294967296)), (35/268435456), by norm_num⟩
  | 3 => ⟨((1125015289/4294967296), (-791083585/4294967296)), (127/1073741824), by norm_num⟩
  | 4 => ⟨((-380824735/2147483648), (535573515/4294967296)), (173/2147483648), by norm_num⟩
  | 5 => ⟨((51564625/536870912), (-290071993/4294967296)), (47/1073741824), by norm_num⟩
  | 6 => ⟨((-46546531/1073741824), (261843173/8589934592)), (341/17179869184), by norm_num⟩
  | 7 => ⟨((1152460275/68719476736), (-810382237/68719476736)), (265/34359738368), by norm_num⟩
  | 8 => ⟨((-390115035/68719476736), (548638945/137438953472)), (361/137438953472), by norm_num⟩
  | 9 => ⟨((939067643/549755813888), (-660329691/549755813888)), (437/549755813888), by norm_num⟩
  | 10 => ⟨((-31788029/68719476736), (715282381/2199023255552)), (119/549755813888), by norm_num⟩
  | 11 => ⟨((250424955/2199023255552), (-352185563/4398046511104)), (471/8796093022208), by norm_num⟩
  | 12 => ⟨((-113027225/4398046511104), (635824123/35184372088832)), (427/35184372088832), by norm_num⟩
  | 13 => ⟨((188359015/35184372088832), (-132449511/35184372088832)), (179/70368744177664), by norm_num⟩
  | 14 => ⟨((-1165910099/1125899906842624), (204959957/281474976710656)), (139/281474976710656), by norm_num⟩
  | 15 => ⟨((420979077/2251799813685248), (-592044643/4503599627370496)), (403/4503599627370496), by norm_num⟩
  | 16 => ⟨((-570016237/18014398509481984), (801643307/36028797018963968)), (137/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (3293964131239/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444589643285015/158456325028528675187087900672), (3896555667661/633825300114114700748351602688)), (185167/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889280063831133/39614081257132168796771975168), (2191358640155/19807040628566084398385987584)), (104181/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889025856840745/2475880078570760549798248448), (2327762893593/1237940039285380274899124224)), (110721/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770691635849191/154742504910672534362390528), (1163568941917/38685626227668133590597632)), (221507/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774542532530991/4835703278458516698824704), (545256959761/1208925819614629174706176)), (103865/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629189184658497/302231454903657293676544), (1907735595947/302231454903657293676544)), (22729/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943562174765463/37778931862957161709568), (387353266947/4722366482869645213696)), (147803/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162129733060193/590295810358705651712), (4646062536133/4722366482869645213696)), (221817/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810378551664559/295147905179352825856), (3192400104525/295147905179352825856)), (305181/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911304433362731/36893488147419103232), (7975698880237/73786976294838206464)), (381749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821680181612359/9223372036854775808), (8965375557015/9223372036854775808)), (107461/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796462631719437/576460752303423488), (8956274027891/1152921504606846976)), (430315/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596824449398965/72057594037927936), (3913254110933/72057594037927936)), (11783/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490231950293055/36028797018963968), (11719318403529/36028797018963968)), (283323/18014398509481984), by norm_num⟩
  | 3 => ⟨((743743766269803/4503599627370496), (14613414291445/9007199254740992)), (710169/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112184015571309/2251799813685248), (14559900092239/2251799813685248)), (356483/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105317571435735/1125899906842624), (10853183565141/562949953421312)), (538229/562949953421312), by norm_num⟩
  | 0 => ⟨((1084703460431533/1125899906842624), (21440309346737/562949953421312)), (2181065/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084703460431533/1125899906842624), (21440309346737/562949953421312)), (8320102695945357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043381247722947/1125899906842624), (41311625660129/562949953421312)), (273041/70368744177664), by norm_num⟩
  | 2 => ⟨((1921694494983873/2251799813685248), (306270745843511/2251799813685248)), (2184531/281474976710656), by norm_num⟩
  | 3 => ⟨((1598325011139227/2251799813685248), (261372615223223/1125899906842624)), (34582537/2251799813685248), by norm_num⟩
  | 4 => ⟨((1013136359375145/2251799813685248), (371043984993011/1125899906842624)), (8143707/281474976710656), by norm_num⟩
  | 5 => ⟨((422551529313207/4503599627370496), (1335529561159863/4503599627370496)), (101565213/2251799813685248), by norm_num⟩
  | 6 => ⟨((-356401444758109/4503599627370496), (501225779557665/9007199254740992)), (79296521/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1117132737/16777216)), (1/8388608), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile030Terms1

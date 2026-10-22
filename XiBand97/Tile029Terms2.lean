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
namespace Reinmann.XiBand97.Tile029Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6223/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6223/256))
  have he : value ((69/80), (6223/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1130746323/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-120322321061911/9007199254740992), (407688504459295/4503599627370496)), (277272637/9007199254740992), by norm_num⟩
  | 1 => ⟨((159074931/4294967296), (-1077988195/4294967296)), (23/268435456), by norm_num⟩
  | 2 => ⟨((-27565585/536870912), (373602239/1073741824)), (1/8388608), by norm_num⟩
  | 3 => ⟨((12738005/268435456), (-1381127139/4294967296)), (475/4294967296), by norm_num⟩
  | 4 => ⟨((-35317249/1073741824), (478662191/2147483648)), (331/4294967296), by norm_num⟩
  | 5 => ⟨((78336165/4294967296), (-530853357/4294967296)), (369/8589934592), by norm_num⟩
  | 6 => ⟨((-72397989/8589934592), (490612677/8589934592)), (343/17179869184), by norm_num⟩
  | 7 => ⟨((57351385/17179869184), (-777295529/34359738368)), (273/34359738368), by norm_num⟩
  | 8 => ⟨((-159011803/137438953472), (1077560409/137438953472)), (95/34359738368), by norm_num⟩
  | 9 => ⟨((195944147/549755813888), (-331959093/137438953472)), (471/549755813888), by norm_num⟩
  | 10 => ⟨((-217309013/2199023255552), (368154415/549755813888)), (131/549755813888), by norm_num⟩
  | 11 => ⟨((219094007/8796093022208), (-1484713861/8796093022208)), (531/8796093022208), by norm_num⟩
  | 12 => ⟨((-101242929/17592186044416), (1372166969/35184372088832)), (493/35184372088832), by norm_num⟩
  | 13 => ⟨((43185385/35184372088832), (-1170601435/140737488355328)), (211/70368744177664), by norm_num⟩
  | 14 => ⟨((-34210089/140737488355328), (927313239/562949953421312)), (671/1125899906842624), by norm_num⟩
  | 15 => ⟨((50586937/1125899906842624), (-1371231055/4503599627370496)), (249/2251799813685248), by norm_num⟩
  | 16 => ⟨((-140256771/18014398509481984), (237616235/4503599627370496)), (347/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (2236982106941/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778277185991399/633825300114114700748351602688), (2645968157141/633825300114114700748351602688)), (184921/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944594383798133/19807040628566084398385987584), (744022869655/9903520314283042199192993792)), (104035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236116150124815/309485009821345068724781056), (3161325484775/2475880078570760549798248448)), (221113/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885297684693435/77371252455336267181195264), (3160457598135/154742504910672534362390528)), (221157/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548995228688677/9671406556917033397649408), (1481003574287/4835703278458516698824704)), (207381/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629150087804705/302231454903657293676544), (2590834720111/604462909807314587353088)), (181505/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471749514670757/18889465931478580854784), (2104189605495/37778931862957161709568)), (36879/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296943822860749/4722366482869645213696), (3154773768715/4722366482869645213696)), (221351/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620628894180403/590295810358705651712), (4335360395755/590295810358705651712)), (9515/18446744073709551616), by norm_num⟩
  | 8 => ⟨((113903140638179/4611686018427387904), (5415522382195/73786976294838206464)), (190393/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910751998115299/4611686018427387904), (6087408835305/9223372036854775808)), (13395/288230376151711744), by norm_num⟩
  | 6 => ⟨((1592751895454343/1152921504606846976), (6081096866499/1152921504606846976)), (13405/36028797018963968), by norm_num⟩
  | 5 => ⟨((1193500364036629/144115188075855872), (5313866126797/144115188075855872)), (93925/36028797018963968), by norm_num⟩
  | 4 => ⟨((745007727130003/18014398509481984), (7956630246533/36028797018963968)), (35267/2251799813685248), by norm_num⟩
  | 3 => ⟨((743613953495213/4503599627370496), (9921033334429/9007199254740992)), (706605/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223881599075531/4503599627370496), (9883983878305/2251799813685248)), (1417011/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104993484179685/1125899906842624), (14733639614047/1125899906842624)), (2135047/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084216517396863/1125899906842624), (58199310812237/2251799813685248)), (4308375/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084216517396863/1125899906842624), (58199310812237/2251799813685248)), (16435146340377043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043324241801915/1125899906842624), (112089278452283/2251799813685248)), (8520445/2251799813685248), by norm_num⟩
  | 2 => ⟨((1928030130119311/2251799813685248), (207736870293033/2251799813685248)), (16639335/2251799813685248), by norm_num⟩
  | 3 => ⟨((1631648405439609/2251799813685248), (355735836398501/2251799813685248)), (31563857/2251799813685248), by norm_num⟩
  | 4 => ⟨((1126089680914201/2251799813685248), (515530560656199/2251799813685248)), (6964375/281474976710656), by norm_num⟩
  | 5 => ⟨((890226746089475/4503599627370496), (1031234909999871/4503599627370496)), (162470701/4503599627370496), by norm_num⟩
  | 6 => ⟨((-120322321061911/9007199254740992), (407688504459295/4503599627370496)), (277272637/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1130746323/16777216)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-577735447/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1518244405118731/18014398509481984), (188673940709495/9007199254740992)), (242716119/18014398509481984), by norm_num⟩
  | 1 => ⟨((-128194997/536870912), (-31861873/536870912)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((1452815105/4294967296), (361085935/4294967296)), (237/4294967296), by norm_num⟩
  | 3 => ⟨((-1372045047/4294967296), (-341011163/4294967296)), (113/2147483648), by norm_num⟩
  | 4 => ⟨((242956021/1073741824), (15096209/268435456)), (81/2147483648), by norm_num⟩
  | 5 => ⟨((-1101353985/8589934592), (-273732997/8589934592)), (185/8589934592), by norm_num⟩
  | 6 => ⟨((520061801/8589934592), (64628665/4294967296)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((-1683938325/68719476736), (-104632455/17179869184)), (287/68719476736), by norm_num⟩
  | 8 => ⟨((1192739133/137438953472), (74111517/34359738368)), (205/137438953472), by norm_num⟩
  | 9 => ⟨((-750952095/274877906944), (-373286647/549755813888)), (65/137438953472), by norm_num⟩
  | 10 => ⟨((1702085997/2199023255552), (105760071/549755813888)), (297/2199023255552), by norm_num⟩
  | 11 => ⟨((-876795047/4398046511104), (-108960307/2199023255552)), (155/4398046511104), by norm_num⟩
  | 12 => ⟨((1656098285/35184372088832), (205805197/17592186044416)), (295/35184372088832), by norm_num⟩
  | 13 => ⟨((-1443716849/140737488355328), (-179412317/70368744177664)), (259/140737488355328), by norm_num⟩
  | 14 => ⟨((1168673669/562949953421312), (290464783/562949953421312)), (211/562949953421312), by norm_num⟩
  | 15 => ⟨((-882960489/2251799813685248), (-109726493/1125899906842624)), (161/2251799813685248), by norm_num⟩
  | 16 => ⟨((156350965/2251799813685248), (77719641/4503599627370496)), (115/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (39665533275/1267650600228229401496703205376)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778200300785797/633825300114114700748351602688), (375308057657/633825300114114700748351602688)), (92237/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472275623677995/9903520314283042199192993792), (422132311401/39614081257132168796771975168)), (103769/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944418914756545/1237940039285380274899124224), (112100958569/618970019642690137449562112)), (55129/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885252163860411/77371252455336267181195264), (224139088819/77371252455336267181195264)), (110261/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387227556828351/2417851639229258349412352), (210063665523/4835703278458516698824704)), (103373/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((19659783583051/9444732965739290427392), (367478010097/604462909807314587353088)), (180909/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943439210722839/37778931862957161709568), (9326589869/1180591620717411303424)), (146995/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40526708371823/147573952589676412928), (223728834739/2361183241434822606848)), (27563/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620507236073289/590295810358705651712), (307449610545/295147905179352825856)), (151605/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822299570598069/73786976294838206464), (384045901841/36893488147419103232)), (379039/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910668196970179/4611686018427387904), (863372104533/9223372036854775808)), (426457/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592586678818105/1152921504606846976), (107807385339/144115188075855872)), (426503/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193358476903611/144115188075855872), (753625847689/144115188075855872)), (373243/144115188075855872), by norm_num⟩
  | 4 => ⟨((372451990586207/9007199254740992), (1128390317353/36028797018963968)), (559971/36028797018963968), by norm_num⟩
  | 3 => ⟨((743488924454295/4503599627370496), (1406910391267/9007199254740992)), (350075/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111704629756171/2251799813685248), (2803117362507/4503599627370496)), (1400867/4503599627370496), by norm_num⟩
  | 1 => ⟨((276168424864105/281474976710656), (4178019055229/2251799813685248)), (2102733/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167426660417567/2251799813685248), (8250017328665/2251799813685248)), (4211303/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167426660417567/2251799813685248), (8250017328665/2251799813685248)), (16064846047408293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2086184676343327/2251799813685248), (3970447860947/562949953421312)), (8137877/2251799813685248), by norm_num⟩
  | 2 => ⟨((966319085307143/1125899906842624), (14713719106623/1125899906842624)), (15193499/2251799813685248), by norm_num⟩
  | 3 => ⟨((1658328729623699/2251799813685248), (25256503712573/1125899906842624)), (13238585/1125899906842624), by norm_num⟩
  | 4 => ⟨((610068131917933/1125899906842624), (74400193945947/2251799813685248)), (20092947/1125899906842624), by norm_num⟩
  | 5 => ⟨((658671834171965/2251799813685248), (161254786714465/4503599627370496)), (2887807/140737488355328), by norm_num⟩
  | 6 => ⟨((1518244405118731/18014398509481984), (188673940709495/9007199254740992)), (242716119/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-577735447/8388608)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-73673865/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((613968154906037/18014398509481984), (-1356724144734765/18014398509481984)), (102873183/4503599627370496), by norm_num⟩
  | 1 => ⟨((-105774177/1073741824), (467471737/2147483648)), (285/4294967296), by norm_num⟩
  | 2 => ⟨((152863347/1073741824), (-1351167107/4294967296)), (207/2147483648), by norm_num⟩
  | 3 => ⟨((-589109201/4294967296), (1301791749/4294967296)), (401/4294967296), by norm_num⟩
  | 4 => ⟨((425686149/4294967296), (-940665527/4294967296)), (73/1073741824), by norm_num⟩
  | 5 => ⟨((-492156489/8589934592), (1087549229/8589934592)), (85/2147483648), by norm_num⟩
  | 6 => ⟨((474171739/17179869184), (-130975899/2147483648)), (165/8589934592), by norm_num⟩
  | 7 => ⟨((-48947593/4294967296), (432650331/17179869184)), (137/17179869184), by norm_num⟩
  | 8 => ⟨((282953481/68719476736), (-625260149/68719476736)), (199/68719476736), by norm_num⟩
  | 9 => ⟨((-181742389/137438953472), (401607617/137438953472)), (257/274877906944), by norm_num⟩
  | 10 => ⟨((420242455/1099511627776), (-928636251/1099511627776)), (299/1099511627776), by norm_num⟩
  | 11 => ⟨((-441693427/4398046511104), (122004727/549755813888)), (79/1099511627776), by norm_num⟩
  | 12 => ⟨((13298523/549755813888), (-940370713/17592186044416)), (153/8796093022208), by norm_num⟩
  | 13 => ⟨((-378463265/70368744177664), (836314139/70368744177664)), (137/35184372088832), by norm_num⟩
  | 14 => ⟨((625085447/562949953421312), (-1381290725/562949953421312)), (455/562949953421312), by norm_num⟩
  | 15 => ⟨((-240897243/1125899906842624), (532325827/1125899906842624)), (11/70368744177664), by norm_num⟩
  | 16 => ⟨((174070647/4503599627370496), (-96163721/1125899906842624)), (1/35184372088832), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-1492577319715/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889061378598413/316912650057057350374175801344), (-1765168156677/633825300114114700748351602688)), (184747/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944507594197401/19807040628566084398385987584), (-62043269787/1237940039285380274899124224)), (25983/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236093121554973/309485009821345068724781056), (-2108934810449/2475880078570760549798248448)), (220881/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770411364902755/154742504910672534362390528), (-131770728715/9671406556917033397649408)), (110455/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548822962414069/9671406556917033397649408), (-1975920309933/9671406556917033397649408)), (207135/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258149680379523/604462909807314587353088), (-864144952999/302231454903657293676544)), (90637/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886753949376601/75557863725914323419136), (-701817738855/18889465931478580854784)), (294627/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296761130284439/4722366482869645213696), (-1052201817557/2361183241434822606848)), (110511/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620378323997269/590295810358705651712), (-2891850445327/590295810358705651712)), (303987/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911068992235965/36893488147419103232), (-451532250711/9223372036854775808)), (95027/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821153997479765/9223372036854775808), (-2030139974607/4611686018427387904)), (427793/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592403519105055/1152921504606846976), (-4055896393413/1152921504606846976)), (428007/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193197356012153/144115188075855872), (-3543983789247/144115188075855872)), (374747/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489564575000421/36028797018963968), (-2653069709625/18014398509481984)), (140651/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486670643304033/9007199254740992), (-3307747081981/4503599627370496)), (704101/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111392995101435/2251799813685248), (-6589790582279/2251799813685248)), (352687/1125899906842624), by norm_num⟩
  | 1 => ⟨((2208390545479711/2251799813685248), (-4910329705479/562949953421312)), (2122511/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082713161917667/1125899906842624), (-19386603528331/1125899906842624)), (4270711/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082713161917667/1125899906842624), (-19386603528331/1125899906842624)), (16291469582564543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((260212285184333/281474976710656), (-18642981207687/562949953421312)), (2090217/562949953421312), by norm_num⟩
  | 2 => ⟨((240247086842427/281474976710656), (-137877485221361/2251799813685248)), (4003085/562949953421312), by norm_num⟩
  | 3 => ⟨((1632020835891305/2251799813685248), (-235364894973541/2251799813685248)), (14647433/1125899906842624), by norm_num⟩
  | 4 => ⟨((1158227014296219/2251799813685248), (-341167461067993/2251799813685248)), (48587637/2251799813685248), by norm_num⟩
  | 5 => ⟨((1088102568184327/4503599627370496), (-350963142821395/2251799813685248)), (129411213/4503599627370496), by norm_num⟩
  | 6 => ⟨((613968154906037/18014398509481984), (-1356724144734765/18014398509481984)), (102873183/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-73673865/1048576)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1200832103/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-551940492611805/9007199254740992), (-447667418291797/9007199254740992)), (520538793/18014398509481984), by norm_num⟩
  | 1 => ⟨((193733585/1073741824), (628533075/4294967296)), (367/4294967296), by norm_num⟩
  | 2 => ⟨((-570436719/2147483648), (-925338643/4294967296)), (543/4294967296), by norm_num⟩
  | 3 => ⟨((559872037/2147483648), (28381283/134217728)), (535/4294967296), by norm_num⟩
  | 4 => ⟨((-824254525/4294967296), (-20891739/134217728)), (99/1073741824), by norm_num⟩
  | 5 => ⟨((970786861/8589934592), (98423121/1073741824)), (469/8589934592), by norm_num⟩
  | 6 => ⟨((-476403779/8589934592), (-386401165/8589934592)), (231/8589934592), by norm_num⟩
  | 7 => ⟨((801566775/34359738368), (650134087/34359738368)), (391/34359738368), by norm_num⟩
  | 8 => ⟨((-295020557/34359738368), (-478570037/68719476736)), (289/68719476736), by norm_num⟩
  | 9 => ⟨((24129723/8589934592), (156568919/68719476736)), (95/68719476736), by norm_num⟩
  | 10 => ⟨((-909420761/1099511627776), (-737612205/1099511627776)), (449/1099511627776), by norm_num⟩
  | 11 => ⟨((121715179/549755813888), (789765137/4398046511104)), (483/4398046511104), by norm_num⟩
  | 12 => ⟨((-238921945/4398046511104), (-387569209/8796093022208)), (119/4398046511104), by norm_num⟩
  | 13 => ⟨((865835185/70368744177664), (702260853/70368744177664)), (433/70368744177664), by norm_num⟩
  | 14 => ⟨((-728399677/281474976710656), (-147697445/70368744177664)), (183/140737488355328), by norm_num⟩
  | 15 => ⟨((1143855147/2251799813685248), (231939261/562949953421312)), (577/2251799813685248), by norm_num⟩
  | 16 => ⟨((-105250365/1125899906842624), (-682931001/9007199254740992)), (427/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-3204597328407/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444511223175037/158456325028528675187087900672), (-1894782078927/316912650057057350374175801344)), (185147/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944463638338839/19807040628566084398385987584), (-4262306864337/39614081257132168796771975168)), (104169/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888651146266515/2475880078570760549798248448), (-1131881597763/618970019642690137449562112)), (221415/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221289633346319/19342813113834066795298816), (-4526205235531/154742504910672534362390528)), (221477/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774367028431147/4835703278458516698824704), (-4241914057619/9671406556917033397649408)), (207701/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314517846855745/151115727451828646838272), (-3710271873475/604462909807314587353088)), (181805/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886625785663915/75557863725914323419136), (-3013281103403/37778931862957161709568)), (147779/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324166047003137/1180591620717411303424), (-2258810833167/2361183241434822606848)), (110889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620243698511781/590295810358705651712), (-6207993997543/590295810358705651712)), (152561/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821967710979027/73786976294838206464), (-7754391760349/73786976294838206464)), (95417/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455239926606085/2305843009213693952), (-4357997258641/4611686018427387904)), (26859/576460752303423488), by norm_num⟩
  | 6 => ⟨((796102909502779/576460752303423488), (-8706381449665/1152921504606846976)), (215101/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193020543789075/144115188075855872), (-3803639482223/72057594037927936)), (376943/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489291733693169/36028797018963968), (-11389333577495/36028797018963968)), (566449/36028797018963968), by norm_num⟩
  | 3 => ⟨((371579077628097/2251799813685248), (-3549737275659/2251799813685248)), (709873/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222037716680195/4503599627370496), (-7071241787761/1125899906842624)), (1425193/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103584968408585/1125899906842624), (-21072950890601/1125899906842624)), (1075723/1125899906842624), by norm_num⟩
  | 0 => ⟨((540649304671989/562949953421312), (-83170277898997/2251799813685248)), (2178875/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((540649304671989/562949953421312), (-83170277898997/2251799813685248)), (8311748508933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1036928195563799/1125899906842624), (-159751156003085/2251799813685248)), (8692153/2251799813685248), by norm_num⟩
  | 2 => ⟨((1898641199449919/2251799813685248), (-294254359427111/2251799813685248)), (4310965/562949953421312), by norm_num⟩
  | 3 => ⟨((1562418095438453/2251799813685248), (-124052645916985/562949953421312)), (16792783/1125899906842624), by norm_num⟩
  | 4 => ⟨((974742669517001/2251799813685248), (-21518575673309/70368744177664)), (61408843/2251799813685248), by norm_num⟩
  | 5 => ⟨((422738283838887/4503599627370496), (-596147455553501/2251799813685248)), (90721749/2251799813685248), by norm_num⟩
  | 6 => ⟨((-551940492611805/9007199254740992), (-447667418291797/9007199254740992)), (520538793/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1200832103/16777216)), (1/8388608), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1221751075/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1148191385891543/18014398509481984), (728537370314201/18014398509481984)), (123843931/9007199254740992), by norm_num⟩
  | 1 => ⟨((410041093/2147483648), (-520349243/4294967296)), (179/4294967296), by norm_num⟩
  | 2 => ⟨((-153546667/536870912), (389706755/2147483648)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((613312941/2147483648), (-24322023/134217728)), (17/268435456), by norm_num⟩
  | 4 => ⟨((-459330343/2147483648), (291449077/2147483648)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((550412293/4294967296), (-698482725/8589934592)), (249/8589934592), by norm_num⟩
  | 6 => ⟨((-274814645/4294967296), (697489081/17179869184)), (251/17179869184), by norm_num⟩
  | 7 => ⟨((940881259/34359738368), (-149249325/8589934592)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((-11010267/1073741824), (111777755/17179869184)), (41/17179869184), by norm_num⟩
  | 9 => ⟨((469103107/137438953472), (-595299961/274877906944)), (55/68719476736), by norm_num⟩
  | 10 => ⟨((-562122927/549755813888), (356671861/549755813888)), (133/549755813888), by norm_num⟩
  | 11 => ⟨((1224705305/4398046511104), (-777086113/4398046511104)), (73/1099511627776), by norm_num⟩
  | 12 => ⟨((-1222963069/17592186044416), (775980649/17592186044416)), (147/8796093022208), by norm_num⟩
  | 13 => ⟨((1127283057/70368744177664), (-357635427/35184372088832)), (273/70368744177664), by norm_num⟩
  | 14 => ⟨((-964868067/281474976710656), (306108569/140737488355328)), (59/70368744177664), by norm_num⟩
  | 15 => ⟨((96349547/140737488355328), (-244538485/562949953421312)), (191/1125899906842624), by norm_num⟩
  | 16 => ⟨((-577274895/4503599627370496), (91571479/1125899906842624)), (9/281474976710656), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (3355768408553/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888988002046645/316912650057057350374175801344), (3968040027187/633825300114114700748351602688)), (92591/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472212438522723/9903520314283042199192993792), (2231514726549/19807040628566084398385987584)), (104191/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472142186350791/618970019642690137449562112), (4740717258405/2475880078570760549798248448)), (110731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55319832147515/4835703278458516698824704), (2369654808217/77371252455336267181195264)), (27691/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387164182932563/2417851639229258349412352), (4441607543825/9671406556917033397649408)), (25969/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258003688529491/604462909807314587353088), (3884911826505/604462909807314587353088)), (90927/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235814462650351/9444732965739290427392), (197193123955/2361183241434822606848)), (147821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162072695031085/590295810358705651712), (4730184392715/4722366482869645213696)), (110923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202516247610535/73786976294838206464), (6500023125813/590295810358705651712)), (152611/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821825407663429/73786976294838206464), (8119061404299/73786976294838206464)), (23863/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227599925119003/1152921504606846976), (9125743830367/9223372036854775808)), (214959/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592045246695629/1152921504606846976), (9115501118991/1152921504606846976)), (215199/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596439872075243/72057594037927936), (7964550879111/144115188075855872)), (94285/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489079939805981/36028797018963968), (11923827243291/36028797018963968)), (283395/36028797018963968), by norm_num⟩
  | 3 => ⟨((743025267660411/4503599627370496), (7432297224731/4503599627370496)), (355193/9007199254740992), by norm_num⟩
  | 2 => ⟨((277687887172617/562949953421312), (29608855176969/4503599627370496)), (356619/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206360438694823/2251799813685248), (689269862499/35184372088832)), (1077009/2251799813685248), by norm_num⟩
  | 0 => ⟨((540237140276455/562949953421312), (87031431852561/2251799813685248)), (68211/70368744177664), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540237140276455/562949953421312), (87031431852561/2251799813685248)), (260204315453982331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2070399058247133/2251799813685248), (83520056396567/1125899906842624)), (4358099/2251799813685248), by norm_num⟩
  | 2 => ⟨((1891220451847829/2251799813685248), (307167351302339/2251799813685248)), (2165153/562949953421312), by norm_num⟩
  | 3 => ⟨((193309980011181/281474976710656), (515961652889727/2251799813685248)), (16910371/2251799813685248), by norm_num⟩
  | 4 => ⟨((471929932588463/1125899906842624), (354349569443887/1125899906842624)), (15488345/1125899906842624), by norm_num⟩
  | 5 => ⟨((345161211285057/4503599627370496), (594113801427925/2251799813685248)), (11366643/562949953421312), by norm_num⟩
  | 6 => ⟨((-1148191385891543/18014398509481984), (728537370314201/18014398509481984)), (123843931/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1221751075/16777216)), (1/16777216), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1241649193/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((234226154970639/18014398509481984), (1282571856471885/18014398509481984)), (398681107/18014398509481984), by norm_num⟩
  | 1 => ⟨((-85008953/2147483648), (-930981349/4294967296)), (291/4294967296), by norm_num⟩
  | 2 => ⟨((258811665/4294967296), (1417196803/4294967296)), (445/4294967296), by norm_num⟩
  | 3 => ⟨((-8207895/134217728), (-1438229155/4294967296)), (227/2147483648), by norm_num⟩
  | 4 => ⟨((49978241/1073741824), (1094680233/4294967296)), (347/4294967296), by norm_num⟩
  | 5 => ⟨((-121727901/4294967296), (-1333111413/8589934592)), (53/1073741824), by norm_num⟩
  | 6 => ⟨((61767221/4294967296), (676447935/8589934592)), (27/1073741824), by norm_num⟩
  | 7 => ⟨((-214916217/34359738368), (-1176834809/34359738368)), (189/17179869184), by norm_num⟩
  | 8 => ⟨((163579311/68719476736), (1791449991/137438953472)), (289/68719476736), by norm_num⟩
  | 9 => ⟨((-221342615/274877906944), (-1212024377/274877906944)), (393/274877906944), by norm_num⟩
  | 10 => ⟨((269553023/1099511627776), (1476014165/1099511627776)), (481/1099511627776), by norm_num⟩
  | 11 => ⟨((-298421901/4398046511104), (-1634093907/4398046511104)), (535/4398046511104), by norm_num⟩
  | 12 => ⟨((302850725/17592186044416), (1658345189/17592186044416)), (545/17592186044416), by norm_num⟩
  | 13 => ⟨((-70925833/17592186044416), (-388374549/17592186044416)), (513/70368744177664), by norm_num⟩
  | 14 => ⟨((246783189/281474976710656), (675665731/140737488355328)), (449/281474976710656), by norm_num⟩
  | 15 => ⟨((-100178261/562949953421312), (-1097109055/1125899906842624)), (183/562949953421312), by norm_num⟩
  | 16 => ⟨((304994963/9007199254740992), (208760821/1125899906842624)), (35/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (905422303225/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777917173186731/633825300114114700748351602688), (1070545334703/316912650057057350374175801344)), (92411/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472195978674355/9903520314283042199192993792), (2408178933261/39614081257132168796771975168)), (12997/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236062406287543/309485009821345068724781056), (2558004785135/2475880078570760549798248448)), (55245/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770165649747865/154742504910672534362390528), (159827132679/9671406556917033397649408)), (27627/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548592611908957/9671406556917033397649408), (9361673671/37778931862957161709568)), (25905/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257948131175667/604462909807314587353088), (2096196707475/604462909807314587353088)), (181373/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943213223017977/37778931862957161709568), (3404786247145/75557863725914323419136)), (294801/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81032219700339/295147905179352825856), (2552248670631/4722366482869645213696)), (110581/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620040623597633/590295810358705651712), (3507164108325/590295810358705651712)), (152099/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910857944859871/36893488147419103232), (4380690749761/73786976294838206464)), (380399/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56896224486273/288230376151711744), (4923792354945/9223372036854775808)), (107039/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591928759130549/1152921504606846976), (2459096057307/576460752303423488)), (3347/9007199254740992), by norm_num⟩
  | 5 => ⟨((1192782002542247/144115188075855872), (2098205877/70368744177664)), (93789/36028797018963968), by norm_num⟩
  | 4 => ⟨((372235417463827/9007199254740992), (6433123018077/36028797018963968)), (563319/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485892235309225/9007199254740992), (8019458053619/9007199254740992)), (88147/1125899906842624), by norm_num⟩
  | 2 => ⟨((555307465691137/1125899906842624), (7986626904695/2251799813685248)), (22085/70368744177664), by norm_num⟩
  | 1 => ⟨((137878633697345/140737488355328), (23796335549703/2251799813685248)), (1063953/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160769028179917/2251799813685248), (11735535632873/562949953421312)), (4286957/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160769028179917/2251799813685248), (11735535632873/562949953421312)), (16353443154341887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1036219827365267/1125899906842624), (90088938707615/2251799813685248)), (2101511/562949953421312), by norm_num⟩
  | 2 => ⟨((118985102482487/140737488355328), (165826365110755/2251799813685248)), (1009099/140737488355328), by norm_num⟩
  | 3 => ⟨((199663063721475/281474976710656), (280392485009905/2251799813685248)), (14839111/1125899906842624), by norm_num⟩
  | 4 => ⟨((549063406138317/1125899906842624), (99447601445411/562949953421312)), (49495261/2251799813685248), by norm_num⟩
  | 5 => ⟨((930495937109403/4503599627370496), (775955851138167/4503599627370496)), (32880727/1125899906842624), by norm_num⟩
  | 6 => ⟨((234226154970639/18014398509481984), (1282571856471885/18014398509481984)), (398681107/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1241649193/16777216)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile029Terms2

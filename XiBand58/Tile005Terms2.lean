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
namespace Reinmann.XiBand58.Tile005Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2697/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2697/160))
  have he : value ((15/16), (2697/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-784090717/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-619589408736219/9007199254740992), (-63389237048761/2251799813685248)), (119546119/9007199254740992), by norm_num⟩
  | 1 => ⟨((819142631/4294967296), (167610439/2147483648)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-567786405/2147483648), (-464714813/4294967296)), (7/134217728), by norm_num⟩
  | 3 => ⟨((524746061/2147483648), (429487683/4294967296)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((-1454905011/8589934592), (-595396353/8589934592)), (73/2147483648), by norm_num⟩
  | 5 => ⟨((806770645/8589934592), (330157843/8589934592)), (41/2147483648), by norm_num⟩
  | 6 => ⟨((-1491228795/34359738368), (-610261275/34359738368)), (153/17179869184), by norm_num⟩
  | 7 => ⟨((147663005/8589934592), (120857395/17179869184)), (61/17179869184), by norm_num⟩
  | 8 => ⟨((-818817565/137438953472), (-167543925/68719476736)), (171/137438953472), by norm_num⟩
  | 9 => ⟨((1008997487/549755813888), (103228977/137438953472)), (213/549755813888), by norm_num⟩
  | 10 => ⟨((-1119014021/2199023255552), (-114484599/549755813888)), (119/1099511627776), by norm_num⟩
  | 11 => ⟨((1128205693/8796093022208), (461699939/8796093022208)), (121/4398046511104), by norm_num⟩
  | 12 => ⟨((-260670865/8796093022208), (-106675337/8796093022208)), (225/35184372088832), by norm_num⟩
  | 13 => ⟨((444758831/70368744177664), (182010361/70368744177664)), (97/70368744177664), by norm_num⟩
  | 14 => ⟨((-704647611/562949953421312), (-576731285/1125899906842624)), (155/562949953421312), by norm_num⟩
  | 15 => ⟨((1041972277/4503599627370496), (106602577/1125899906842624)), (231/4503599627370496), by norm_num⟩
  | 16 => ⟨((-361120073/9007199254740992), (-295565103/18014398509481984)), (323/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (-3586287230405/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777950956801817/633825300114114700748351602688), (-4240509360843/633825300114114700748351602688)), (46309/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888821516417229/39614081257132168796771975168), (-4769478509821/39614081257132168796771975168)), (104223/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((7377104150463/9671406556917033397649408), (-5066225089791/2475880078570760549798248448)), (110767/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770204455536917/154742504910672534362390528), (-1266177836511/38685626227668133590597632)), (55401/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548628348511997/9671406556917033397649408), (-593319867261/1208925819614629174706176)), (51957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39311836170289/18889465931478580854784), (-4151631575715/604462909807314587353088)), (90963/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886475008839885/75557863725914323419136), (-842923527681/9444732965739290427392)), (147883/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296550884238999/4722366482869645213696), (-631863209685/590295810358705651712)), (55487/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810043773523967/295147905179352825856), (-3473107222957/295147905179352825856)), (9543/36893488147419103232), by norm_num⟩
  | 8 => ⟨((910885992269911/36893488147419103232), (-4338174965763/36893488147419103232)), (191009/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455184694341205/2305843009213693952), (-4876036946963/4611686018427387904)), (107545/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397995992872151/288230376151711744), (-4870528443771/576460752303423488)), (215347/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192825397464487/144115188075855872), (-8511041258085/144115188075855872)), (188717/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488996963489701/36028797018963968), (-1592727673855/4503599627370496)), (141827/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485944278711809/9007199254740992), (-7942020302273/4503599627370496)), (355583/9007199254740992), by norm_num⟩
  | 2 => ⟨((555320756139713/1125899906842624), (-15819305916341/2251799813685248)), (357107/2251799813685248), by norm_num⟩
  | 1 => ⟨((551502900385921/562949953421312), (-23567540641759/1125899906842624)), (539483/1125899906842624), by norm_num⟩
  | 0 => ⟨((540044249347177/562949953421312), (-23245960390493/562949953421312)), (1094323/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((540044249347177/562949953421312), (-23245960390493/562949953421312)), (4174510960105514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((64638831304915/70368744177664), (-178400899094385/2251799813685248)), (4379939/2251799813685248), by norm_num⟩
  | 2 => ⟨((235735204466111/281474976710656), (-327748512666151/2251799813685248)), (4370299/1125899906842624), by norm_num⟩
  | 3 => ⟨((1531721619063383/2251799813685248), (-274489276274959/1125899906842624)), (8592439/1125899906842624), by norm_num⟩
  | 4 => ⟨((454035401974717/1125899906842624), (-746853527771337/2251799813685248)), (31758223/2251799813685248), by norm_num⟩
  | 5 => ⟨((236968127823261/4503599627370496), (-301179473980801/1125899906842624)), (93360799/4503599627370496), by norm_num⟩
  | 6 => ⟨((-619589408736219/9007199254740992), (-63389237048761/2251799813685248)), (119546119/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-784090717/16777216)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-1602470835/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-254882267717481/4503599627370496), (187193586168633/4503599627370496)), (231640231/18014398509481984), by norm_num⟩
  | 1 => ⟨((344341203/2147483648), (-252895053/2147483648)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-975592091/4294967296), (716505639/4294967296)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((460676755/2147483648), (-676671113/4294967296)), (27/536870912), by norm_num⟩
  | 4 => ⟨((-652597765/4294967296), (479288407/4294967296)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((369789739/4294967296), (-135792631/2147483648)), (89/4294967296), by norm_num⟩
  | 6 => ⟨((-698462149/17179869184), (512972659/17179869184)), (85/8589934592), by norm_num⟩
  | 7 => ⟨((1130795589/68719476736), (-415245995/34359738368)), (277/68719476736), by norm_num⟩
  | 8 => ⟨((-50059143/8589934592), (588240247/137438953472)), (99/68719476736), by norm_num⟩
  | 9 => ⟨((252139079/137438953472), (-92589451/68719476736)), (251/549755813888), by norm_num⟩
  | 10 => ⟨((-1142982085/2199023255552), (419721069/1099511627776)), (143/1099511627776), by norm_num⟩
  | 11 => ⟨((1177568035/8796093022208), (-54052697/549755813888)), (297/8796093022208), by norm_num⟩
  | 12 => ⟨((-556050245/17592186044416), (102095215/4398046511104)), (283/35184372088832), by norm_num⟩
  | 13 => ⟨((484741223/70368744177664), (-178004631/35184372088832)), (249/140737488355328), by norm_num⟩
  | 14 => ⟨((-784785887/562949953421312), (288185769/281474976710656)), (51/140737488355328), by norm_num⟩
  | 15 => ⟨((296462113/1125899906842624), (-870924551/4503599627370496)), (155/2251799813685248), by norm_num⟩
  | 16 => ⟨((-839940415/18014398509481984), (616878765/18014398509481984)), (111/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (3267119379865/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444466265119329/158456325028528675187087900672), (1931377602215/316912650057057350374175801344)), (23145/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888724996674159/39614081257132168796771975168), (2172293317111/19807040628566084398385987584)), (52089/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888436258657329/2475880078570760549798248448), (2307435564673/1237940039285380274899124224)), (110717/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885051109228887/77371252455336267181195264), (1153365705855/38685626227668133590597632)), (55375/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548532678339895/9671406556917033397649408), (2161812750835/4835703278458516698824704)), (51931/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157236902875935/75557863725914323419136), (472709612709/75557863725914323419136)), (90913/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886339596892029/75557863725914323419136), (383901380841/4722366482869645213696)), (147797/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296449615080477/4722366482869645213696), (2302182541739/2361183241434822606848)), (110903/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404987193090877/147573952589676412928), (6327020247899/590295810358705651712)), (76291/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821599220887117/73786976294838206464), (7902806063369/73786976294838206464)), (190863/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910272692872115/4611686018427387904), (8882454576785/9223372036854775808)), (53727/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795895893507091/576460752303423488), (1109026246731/144115188075855872)), (107571/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192658591046533/144115188075855872), (7751669825131/144115188075855872)), (188513/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488749456260303/36028797018963968), (2901126279325/9007199254740992)), (8853/1125899906842624), by norm_num⟩
  | 3 => ⟨((742819803401189/4503599627370496), (7232722726983/4503599627370496)), (355045/9007199254740992), by norm_num⟩
  | 2 => ⟨((555171937242693/1125899906842624), (28810586551111/4503599627370496)), (356433/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205153620760477/2251799813685248), (42916005624063/2251799813685248)), (1076267/2251799813685248), by norm_num⟩
  | 0 => ⟨((269824917845571/281474976710656), (84637830846023/2251799813685248)), (2180525/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((269824917845571/281474976710656), (84637830846023/2251799813685248)), (8318042763716887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258259389439203/281474976710656), (81134728285745/1125899906842624)), (1086117/562949953421312), by norm_num⟩
  | 2 => ⟨((470993800228817/562949953421312), (74442871029817/562949953421312)), (8598431/2251799813685248), by norm_num⟩
  | 3 => ⟨((384214293814759/562949953421312), (249131422878273/1125899906842624)), (1041367/140737488355328), by norm_num⟩
  | 4 => ⟨((938655426134259/2251799813685248), (680130467204107/2251799813685248)), (30117163/2251799813685248), by norm_num⟩
  | 5 => ⟨((92924902570959/1125899906842624), (1134040689834783/4503599627370496)), (43301575/2251799813685248), by norm_num⟩
  | 6 => ⟨((-254882267717481/4503599627370496), (187193586168633/4503599627370496)), (231640231/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-1602470835/33554432)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-817399871/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((15670207624687/9007199254740992), (599271145382433/9007199254740992)), (193269759/18014398509481984), by norm_num⟩
  | 1 => ⟨((-43194509/8589934592), (-825937459/4294967296)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((31212047/4294967296), (1193633153/4294967296)), (195/4294967296), by norm_num⟩
  | 3 => ⟨((-30071473/4294967296), (-575007259/2147483648)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((10864717/2147483648), (830992371/4294967296)), (277/8589934592), by norm_num⟩
  | 5 => ⟨((-25122457/8589934592), (-1921501505/17179869184)), (323/17179869184), by norm_num⟩
  | 6 => ⟨((48408827/34359738368), (1851284561/34359738368)), (313/34359738368), by norm_num⟩
  | 7 => ⟨((-19988501/34359738368), (-764414373/34359738368)), (65/17179869184), by norm_num⟩
  | 8 => ⟨((28887099/137438953472), (552360429/68719476736)), (95/68719476736), by norm_num⟩
  | 9 => ⟨((-37108647/549755813888), (-1419135097/549755813888)), (123/274877906944), by norm_num⟩
  | 10 => ⟨((21451557/1099511627776), (820365601/1099511627776)), (143/1099511627776), by norm_num⟩
  | 11 => ⟨((-2818317/549755813888), (-862240569/4398046511104)), (303/8796093022208), by norm_num⟩
  | 12 => ⟨((43445247/35184372088832), (415365965/8796093022208)), (147/17592186044416), by norm_num⟩
  | 13 => ⟨((-9659455/35184372088832), (-1477614837/140737488355328)), (263/140737488355328), by norm_num⟩
  | 14 => ⟨((498561/8796093022208), (1220244627/562949953421312)), (219/562949953421312), by norm_num⟩
  | 15 => ⟨((-24593521/2251799813685248), (-940522829/2251799813685248)), (85/1125899906842624), by norm_num⟩
  | 16 => ⟨((35542209/18014398509481984), (169903789/2251799813685248)), (31/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (2012083654369/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777787503790219/633825300114114700748351602688), (2378700530135/633825300114114700748351602688)), (92435/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888638039096289/39614081257132168796771975168), (2675410236019/39614081257132168796771975168)), (26001/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472086064310751/618970019642690137449562112), (2841837645047/2475880078570760549798248448)), (55261/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770010656472847/154742504910672534362390528), (710238521751/38685626227668133590597632)), (55271/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548447305509243/9671406556917033397649408), (2662456023301/9671406556917033397649408)), (51827/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257820987901851/604462909807314587353088), (291088872213/75557863725914323419136)), (45359/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471554959488495/18889465931478580854784), (14774989603/295147905179352825856)), (147455/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648180279489475/2361183241434822606848), (708815145667/1180591620717411303424)), (55313/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809913779319233/295147905179352825856), (1947993272933/295147905179352825856)), (76083/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821449558509415/73786976294838206464), (4866240767213/73786976294838206464)), (47573/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820379561274561/9223372036854775808), (683672431961/1152921504606846976)), (214193/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591629137761699/1152921504606846976), (5462959311003/1152921504606846976)), (107169/576460752303423488), by norm_num⟩
  | 5 => ⟨((596259917788345/72057594037927936), (1193218955145/36028797018963968)), (46927/36028797018963968), by norm_num⟩
  | 4 => ⟨((372137106154131/9007199254740992), (7144909266801/36028797018963968)), (281887/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485400691789545/9007199254740992), (8905979748807/9007199254740992)), (352929/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110123415193637/2251799813685248), (17736692539197/4503599627370496)), (176893/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204583781435823/2251799813685248), (3302197773317/281474976710656)), (1065661/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157821398650333/2251799813685248), (52089589459767/2251799813685248)), (1074311/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2157821398650333/2251799813685248), (52089589459767/2251799813685248)), (4098171238425826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1033280097738219/1125899906842624), (99831281715265/2251799813685248)), (2108653/1125899906842624), by norm_num⟩
  | 2 => ⟨((1892133008815611/2251799813685248), (183237738809937/2251799813685248)), (8114697/2251799813685248), by norm_num⟩
  | 3 => ⟨((1575002907705709/2251799813685248), (76985123623311/562949953421312)), (7478909/1125899906842624), by norm_num⟩
  | 4 => ⟨((16554860337669/35184372088832), (107693226387083/562949953421312)), (12507651/1125899906842624), by norm_num⟩
  | 5 => ⟨((416110876209575/2251799813685248), (810744642035901/4503599627370496)), (66222413/4503599627370496), by norm_num⟩
  | 6 => ⟨((15670207624687/9007199254740992), (599271145382433/9007199254740992)), (193269759/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-817399871/16777216)), (1/16777216), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-208172533/4194304)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((229673713741009/4503599627370496), (674464400217347/18014398509481984)), (22337063/2251799813685248), by norm_num⟩
  | 1 => ⟨((-322466009/2147483648), (-473480051/4294967296)), (1/33554432), by norm_num⟩
  | 2 => ⟨((474740743/2147483648), (697066559/4294967296)), (95/2147483648), by norm_num⟩
  | 3 => ⟨((-465948383/2147483648), (-684156649/4294967296)), (47/1073741824), by norm_num⟩
  | 4 => ⟨((685978291/4294967296), (62951797/536870912)), (35/1073741824), by norm_num⟩
  | 5 => ⟨((-100991061/1073741824), (-37071545/536870912)), (167/8589934592), by norm_num⟩
  | 6 => ⟨((792965377/17179869184), (291079739/8589934592)), (83/8589934592), by norm_num⟩
  | 7 => ⟨((-667096619/34359738368), (-489752303/34359738368)), (71/17179869184), by norm_num⟩
  | 8 => ⟨((245528161/34359738368), (360511443/68719476736)), (211/137438953472), by norm_num⟩
  | 9 => ⟨((-321307861/137438953472), (-471779531/274877906944)), (35/68719476736), by norm_num⟩
  | 10 => ⟨((94607139/137438953472), (34728151/68719476736)), (167/1099511627776), by norm_num⟩
  | 11 => ⟨((-810370757/4398046511104), (-594937725/4398046511104)), (45/1099511627776), by norm_num⟩
  | 12 => ⟨((795362415/17592186044416), (145979819/4398046511104)), (89/8796093022208), by norm_num⟩
  | 13 => ⟨((-720583415/70368744177664), (-529019901/70368744177664)), (163/70368744177664), by norm_num⟩
  | 14 => ⟨((303101985/140737488355328), (222523831/140737488355328)), (69/140737488355328), by norm_num⟩
  | 15 => ⟨((-475981493/1125899906842624), (-698888365/2251799813685248)), (219/2251799813685248), by norm_num⟩
  | 16 => ⟨((700749231/9007199254740992), (64307317/1125899906842624)), (163/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (206230431205/2535301200456458802993406410752)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1777711974666445/633825300114114700748351602688), (975147041503/633825300114114700748351602688)), (34611/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944276613652255/19807040628566084398385987584), (548390060413/19807040628566084398385987584)), (9735/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888254355722463/2475880078570760549798248448), (582500468645/1237940039285380274899124224)), (82753/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442480248017999/38685626227668133590597632), (291158049801/38685626227668133590597632)), (82759/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387090874219373/2417851639229258349412352), (545725532429/4835703278458516698824704)), (77593/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628873953436407/302231454903657293676544), (238657060641/151115727451828646838272)), (16975/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886101552421035/75557863725914323419136), (1550537333739/75557863725914323419136)), (220699/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296272256608691/4722366482869645213696), (1162261522739/4722366482869645213696)), (82773/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((6326979731037/2305843009213693952), (48738645/18014398509481984)), (56915/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821299625011921/73786976294838206464), (498693414551/18446744073709551616)), (284627/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820212259800659/9223372036854775808), (1120987860985/4611686018427387904)), (320277/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795731774853101/576460752303423488), (559824502145/288230376151711744)), (320367/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192376868517761/144115188075855872), (489094393679/36028797018963968)), (280421/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488337806269221/36028797018963968), (732140148101/9007199254740992)), (210417/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485144096690599/9007199254740992), (1825107220201/4503599627370496)), (526399/9007199254740992), by norm_num⟩
  | 2 => ⟨((277469194964751/562949953421312), (3634532474121/2251799813685248)), (263467/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101946638497343/1125899906842624), (2706379748115/562949953421312)), (395875/562949953421312), by norm_num⟩
  | 0 => ⟨((1078317812852585/1125899906842624), (21340704811619/2251799813685248)), (3177895/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1078317812852585/1125899906842624), (21340704811619/2251799813685248)), (12122707375533293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065290958865373/2251799813685248), (40877633966115/2251799813685248)), (3073711/1125899906842624), by norm_num⟩
  | 2 => ⟨((473371982036273/562949953421312), (37491879756335/1125899906842624)), (5749849/1125899906842624), by norm_num⟩
  | 3 => ⟨((794847292393661/1125899906842624), (126104321157939/2251799813685248)), (20105545/2251799813685248), by norm_num⟩
  | 4 => ⟨((557604312298439/1125899906842624), (44512694966205/562949953421312)), (7659889/562949953421312), by norm_num⟩
  | 5 => ⟨((67278860047803/281474976710656), (352720102585819/4503599627370496)), (70387953/4503599627370496), by norm_num⟩
  | 6 => ⟨((229673713741009/4503599627370496), (674464400217347/18014398509481984)), (22337063/2251799813685248), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-208172533/4194304)), (3/33554432), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-1694391849/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1057252471236767/18014398509481984), (-249031986629957/18014398509481984)), (41930775/9007199254740992), by norm_num⟩
  | 1 => ⟨((-94391267/536870912), (88934083/2147483648)), (61/4294967296), by norm_num⟩
  | 2 => ⟨((282770965/1073741824), (-266422703/4294967296)), (93/4294967296), by norm_num⟩
  | 3 => ⟨((-141184351/536870912), (266043697/4294967296)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((1691802067/8589934592), (-398497845/8589934592)), (145/8589934592), by norm_num⟩
  | 5 => ⟨((-1013637211/8589934592), (238758571/8589934592)), (89/8589934592), by norm_num⟩
  | 6 => ⟨((253048809/4294967296), (-238418919/17179869184)), (91/17179869184), by norm_num⟩
  | 7 => ⟨((-27073803/1073741824), (204068357/34359738368)), (79/34359738368), by norm_num⟩
  | 8 => ⟨((1297693847/137438953472), (-152833541/68719476736)), (15/17179869184), by norm_num⟩
  | 9 => ⟨((-107987315/34359738368), (203488165/274877906944)), (81/274877906944), by norm_num⟩
  | 10 => ⟨((1035203471/1099511627776), (-243838425/1099511627776)), (99/1099511627776), by norm_num⟩
  | 11 => ⟨((-1127706345/4398046511104), (132813571/2199023255552)), (55/2199023255552), by norm_num⟩
  | 12 => ⟨((563051049/8796093022208), (-265249267/17592186044416)), (7/1099511627776), by norm_num⟩
  | 13 => ⟨((-1038000123/70368744177664), (122248583/35184372088832)), (105/70368744177664), by norm_num⟩
  | 14 => ⟨((888448705/281474976710656), (-26158859/35184372088832)), (23/70368744177664), by norm_num⟩
  | 15 => ⟨((-44359241/70368744177664), (334357069/2251799813685248)), (149/2251799813685248), by norm_num⟩
  | 16 => ⟨((1063107279/9007199254740992), (-125205533/4503599627370496)), (57/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (-150666366547/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777638373235779/633825300114114700748351602688), (-356179705155/633825300114114700748351602688)), (23059/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888470469661615/39614081257132168796771975168), (-400605645823/39614081257132168796771975168)), (12971/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472041620806529/618970019642690137449562112), (-212760822383/1237940039285380274899124224)), (6891/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769833184200951/154742504910672534362390528), (-425384635349/154742504910672534362390528)), (110259/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774140622808723/4835703278458516698824704), (-49831573179/1208925819614629174706176)), (103371/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628838002794139/302231454903657293676544), (-174337786087/302231454903657293676544)), (90453/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885984841290267/75557863725914323419136), (-566325253573/75557863725914323419136)), (146991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296184835551829/4722366482869645213696), (-424505606715/4722366482869645213696)), (110249/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809793394731309/295147905179352825856), (-72913524529/73786976294838206464)), (151601/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113821866934949/4611686018427387904), (-182138803355/18446744073709551616)), (94757/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820044161360625/9223372036854775808), (-818827862919/9223372036854775808)), (213221/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591295918990677/1152921504606846976), (-408916554417/576460752303423488)), (213243/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192230716648435/144115188075855872), (-714486500669/144115188075855872)), (93307/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488119625526715/36028797018963968), (-66843679837/2251799813685248)), (279971/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484873196495133/9007199254740992), (-666489348797/4503599627370496)), (175027/4503599627370496), by norm_num⟩
  | 2 => ⟨((277402151263865/562949953421312), (-2654309128041/4503599627370496)), (700383/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203102287477955/2251799813685248), (-247029383331/140737488355328)), (525637/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155107236912361/2251799813685248), (-3894862760231/1125899906842624)), (1052707/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2155107236912361/2251799813685248), (-3894862760231/1125899906842624)), (4015758518699264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2062539704702869/2251799813685248), (-7455233693813/1125899906842624)), (2022291/1125899906842624), by norm_num⟩
  | 2 => ⟨((944543934497517/1125899906842624), (-3414316718537/281474976710656)), (7462847/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584468952944423/2251799813685248), (-45829610640845/2251799813685248)), (12702567/2251799813685248), by norm_num⟩
  | 4 => ⟨((1113971807968153/2251799813685248), (-64495604577841/2251799813685248)), (4598317/562949953421312), by norm_num⟩
  | 5 => ⟨((1098475538030973/4503599627370496), (-63812320083635/2251799813685248)), (9626019/1125899906842624), by norm_num⟩
  | 6 => ⟨((1057252471236767/18014398509481984), (-249031986629957/18014398509481984)), (41930775/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1694391849/33554432)), (1/16777216), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-1721987659/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((512912820757877/18014398509481984), (-901986623252141/18014398509481984)), (69045051/9007199254740992), by norm_num⟩
  | 1 => ⟨((-744616791/8589934592), (327362837/2147483648)), (203/8589934592), by norm_num⟩
  | 2 => ⟨((70843829/536870912), (-996663503/4294967296)), (39/1073741824), by norm_num⟩
  | 3 => ⟨((-71895209/536870912), (1011454799/4294967296)), (5/134217728), by norm_num⟩
  | 4 => ⟨((218886577/2147483648), (-96231151/536870912)), (123/4294967296), by norm_num⟩
  | 5 => ⟨((-133281019/2147483648), (937529275/8589934592)), (151/8589934592), by norm_num⟩
  | 6 => ⟨((541036071/17179869184), (-951442971/17179869184)), (155/17179869184), by norm_num⟩
  | 7 => ⟨((-470627559/34359738368), (206906391/8589934592)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((358209041/68719476736), (-314965575/34359738368)), (211/137438953472), by norm_num⟩
  | 9 => ⟨((-242350103/137438953472), (6659165/2147483648)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((590272261/1099511627776), (-259506909/274877906944)), (89/549755813888), by norm_num⟩
  | 11 => ⟨((-326744935/2199023255552), (1149199429/4398046511104)), (199/4398046511104), by norm_num⟩
  | 12 => ⟨((663188191/17592186044416), (-1166254483/17592186044416)), (51/4398046511104), by norm_num⟩
  | 13 => ⟨((-310629435/35184372088832), (1092519367/70368744177664)), (193/70368744177664), by norm_num⟩
  | 14 => ⟨((33775653/17592186044416), (-950342779/281474976710656)), (85/140737488355328), by norm_num⟩
  | 15 => ⟨((-438744463/1125899906842624), (771557311/1125899906842624)), (35/281474976710656), by norm_num⟩
  | 16 => ⟨((667883681/9007199254740992), (-1174511773/9007199254740992)), (215/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (-343156399691/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888783302053587/316912650057057350374175801344), (-1622340940323/633825300114114700748351602688)), (11545/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888389675843049/39614081257132168796771975168), (-456171462473/9903520314283042199192993792)), (25979/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888080565645875/2475880078570760549798248448), (-1938164511469/2475880078570760549798248448)), (110423/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884873591667199/77371252455336267181195264), (-484382529273/38685626227668133590597632)), (27609/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548200531403525/9671406556917033397649408), (-907880360709/4835703278458516698824704)), (25887/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257605292351183/604462909807314587353088), (-794058591891/302231454903657293676544)), (90619/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885869766933383/75557863725914323419136), (-2579428380587/75557863725914323419136)), (73641/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648049192660703/2361183241434822606848), (-1933467668291/4722366482869645213696)), (110485/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809733843023719/295147905179352825856), (-664181480607/147573952589676412928)), (151955/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455250160218283/18446744073709551616), (-3318221417831/73786976294838206464)), (190001/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819875796284965/9223372036854775808), (-932327358093/2305843009213693952)), (106915/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591126954092889/1152921504606846976), (-3724702698933/1152921504606846976)), (213929/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192082199914759/144115188075855872), (-1626969813369/72057594037927936)), (187299/144115188075855872), by norm_num⟩
  | 4 => ⟨((743947755697413/18014398509481984), (-4870577294277/36028797018963968)), (281171/36028797018963968), by norm_num⟩
  | 3 => ⟨((742295361840595/4503599627370496), (-3035090758695/4503599627370496)), (351855/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109322663229587/2251799813685248), (-12086406983701/4503599627370496)), (352443/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202227299525823/2251799813685248), (-17995293568249/2251799813685248)), (1060287/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076644849737985/1125899906842624), (-35456745619373/2251799813685248)), (266561/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1076644849737985/1125899906842624), (-35456745619373/2251799813685248)), (1016849518896007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1029265417131641/1125899906842624), (-2119100592755/70368744177664)), (259097/140737488355328), by norm_num⟩
  | 2 => ⟨((234975973911463/281474976710656), (-123982144688505/2251799813685248)), (7829171/2251799813685248), by norm_num⟩
  | 3 => ⟨((97652601560567/140737488355328), (-51750293287635/562949953421312)), (13933757/2251799813685248), by norm_num⟩
  | 4 => ⟨((1065092168128909/2251799813685248), (-143630551606859/1125899906842624)), (5474507/562949953421312), by norm_num⟩
  | 5 => ⟨((934276998156827/4503599627370496), (-16984166919587/140737488355328)), (52604801/4503599627370496), by norm_num⟩
  | 6 => ⟨((512912820757877/18014398509481984), (-901986623252141/18014398509481984)), (69045051/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-1721987659/33554432)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile005Terms2

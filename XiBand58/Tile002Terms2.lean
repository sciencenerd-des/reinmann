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
namespace Reinmann.XiBand58.Tile002Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2403/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2403/160))
  have he : value ((15/16), (2403/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-698616979/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-932732303061559/18014398509481984), (960593096170117/18014398509481984)), (245555259/18014398509481984), by norm_num⟩
  | 1 => ⟨((308285125/2147483648), (-634987255/4294967296)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-854747861/4294967296), (880279251/4294967296)), (229/4294967296), by norm_num⟩
  | 3 => ⟨((98744345/536870912), (-813550775/4294967296)), (107/2147483648), by norm_num⟩
  | 4 => ⟨((-547554915/4294967296), (281955213/2147483648)), (75/2147483648), by norm_num⟩
  | 5 => ⟨((607257833/8589934592), (-625396675/8589934592)), (21/1073741824), by norm_num⟩
  | 6 => ⟨((-280612703/8589934592), (72248657/2147483648)), (157/17179869184), by norm_num⟩
  | 7 => ⟨((889169847/68719476736), (-57233089/4294967296)), (251/68719476736), by norm_num⟩
  | 8 => ⟨((-616325573/137438953472), (158683817/34359738368)), (11/8589934592), by norm_num⟩
  | 9 => ⟨((379737185/274877906944), (-782159931/549755813888)), (219/549755813888), by norm_num⟩
  | 10 => ⟨((-842284029/2199023255552), (433721561/1099511627776)), (245/2199023255552), by norm_num⟩
  | 11 => ⟨((424601309/4398046511104), (-437284185/4398046511104)), (249/8796093022208), by norm_num⟩
  | 12 => ⟨((-784829867/35184372088832), (25258525/1099511627776)), (29/4398046511104), by norm_num⟩
  | 13 => ⟨((669541673/140737488355328), (-344770469/70368744177664)), (25/17592186044416), by norm_num⟩
  | 14 => ⟨((-265194813/281474976710656), (68279051/70368744177664)), (5/17592186044416), by norm_num⟩
  | 15 => ⟨((392147279/2251799813685248), (-807721501/4503599627370496)), (239/4503599627370496), by norm_num⟩
  | 16 => ⟨((-271815781/9007199254740992), (559869881/18014398509481984)), (167/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (762509874029/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55561050773615/19807040628566084398385987584), (3606437578275/633825300114114700748351602688)), (23139/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236103083036949/4951760157141521099596496896), (4056317515735/39614081257132168796771975168)), (26037/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((29508471916903/38685626227668133590597632), (4308693472021/2475880078570760549798248448)), (110683/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885104107730609/77371252455336267181195264), (4307406968495/154742504910672534362390528)), (110713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548632106750293/9671406556917033397649408), (2018413760681/4835703278458516698824704)), (51913/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157247784875865/75557863725914323419136), (882714504357/151115727451828646838272)), (90879/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886481167985809/75557863725914323419136), (5735083860283/75557863725914323419136)), (147737/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296555885190359/4722366482869645213696), (4299073480801/4722366482869645213696)), (110855/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620095042607343/590295810358705651712), (1476897192795/147573952589676412928)), (76255/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821782281404917/73786976294838206464), (7379033187067/73786976294838206464)), (47691/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910375817081359/4611686018427387904), (8293919836759/9223372036854775808)), (214785/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591998415762987/1152921504606846976), (4142280907799/576460752303423488)), (215003/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192839817234579/144115188075855872), (7238474264403/144115188075855872)), (188373/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489022143020839/36028797018963968), (5418351430787/18014398509481984)), (70763/9007199254740992), by norm_num⟩
  | 3 => ⟨((185747742255721/1125899906842624), (6754586183563/4503599627370496)), (354677/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110688394395173/2251799813685248), (26908460865813/4503599627370496)), (711947/4503599627370496), by norm_num⟩
  | 1 => ⟨((551549495190171/562949953421312), (5011100329571/281474976710656)), (1074421/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160730410253195/2251799813685248), (79086971404727/2251799813685248)), (543741/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2160730410253195/2251799813685248), (79086971404727/2251799813685248)), (2074207308055686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((517641613656191/562949953421312), (37944230905977/562949953421312)), (2163391/1125899906842624), by norm_num⟩
  | 2 => ⟨((946844649012985/1125899906842624), (279122686423435/2251799813685248)), (8540365/2251799813685248), by norm_num⟩
  | 3 => ⟨((389482855232199/562949953421312), (58683240946191/281474976710656)), (16481579/2251799813685248), by norm_num⟩
  | 4 => ⟨((979994776514781/2251799813685248), (649609894424019/2251799813685248)), (29678225/2251799813685248), by norm_num⟩
  | 5 => ⟨((478192371977811/4503599627370496), (1130854171740937/4503599627370496)), (85911323/4503599627370496), by norm_num⟩
  | 6 => ⟨((-932732303061559/18014398509481984), (960593096170117/18014398509481984)), (245555259/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-698616979/16777216)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-1427785471/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((176292429578633/18014398509481984), (78287918250541/1125899906842624)), (98156439/9007199254740992), by norm_num⟩
  | 1 => ⟨((-238167793/8589934592), (-846124171/4294967296)), (267/8589934592), by norm_num⟩
  | 2 => ⟨((84347521/2147483648), (599312573/2147483648)), (191/4294967296), by norm_num⟩
  | 3 => ⟨((-39829087/1073741824), (-1131986919/4294967296)), (91/2147483648), by norm_num⟩
  | 4 => ⟨((112844301/4294967296), (801790111/4294967296)), (65/2147483648), by norm_num⟩
  | 5 => ⟨((-15985599/1073741824), (-1817313953/17179869184)), (297/17179869184), by norm_num⟩
  | 6 => ⟨((241549933/34359738368), (1716279381/34359738368)), (283/34359738368), by norm_num⟩
  | 7 => ⟨((-195532141/68719476736), (-173663773/8589934592)), (231/68719476736), by norm_num⟩
  | 8 => ⟨((34624017/34359738368), (492026519/68719476736)), (165/137438953472), by norm_num⟩
  | 9 => ⟨((-87197535/274877906944), (-619562711/274877906944)), (105/274877906944), by norm_num⟩
  | 10 => ⟨((12352461/137438953472), (87767667/137438953472)), (15/137438953472), by norm_num⟩
  | 11 => ⟨((-203619825/8796093022208), (-361693855/2199023255552)), (249/8796093022208), by norm_num⟩
  | 12 => ⟨((48074867/8796093022208), (683170571/17592186044416)), (237/35184372088832), by norm_num⟩
  | 13 => ⟨((-83819295/70368744177664), (-297779689/35184372088832)), (209/140737488355328), by norm_num⟩
  | 14 => ⟨((135701683/562949953421312), (482099079/281474976710656)), (171/562949953421312), by norm_num⟩
  | 15 => ⟨((-205051637/4503599627370496), (-1456948847/4503599627370496)), (65/1125899906842624), by norm_num⟩
  | 16 => ⟨((145238759/18014398509481984), (1031961729/18014398509481984)), (93/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (932001860337/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222233807244585/79228162514264337593543950336), (1101917199213/316912650057057350374175801344)), (92417/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888731364179593/39614081257132168796771975168), (309842913285/4951760157141521099596496896)), (6499/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((118027713728177/154742504910672534362390528), (1316475610907/1237940039285380274899124224)), (110499/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770109823917573/154742504910672534362390528), (2632148840339/154742504910672534362390528)), (110517/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193567535039831/1208925819614629174706176), (1233393660235/4835703278458516698824704)), (103629/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257902346165565/604462909807314587353088), (539396760049/151115727451828646838272)), (90695/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886352055028315/75557863725914323419136), (3504482441003/75557863725914323419136)), (18427/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296459730391601/4722366482869645213696), (1313482820727/2361183241434822606848)), (55297/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619963933219841/590295810358705651712), (1804905175193/295147905179352825856)), (76059/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455405011849925/18446744073709551616), (4508864278277/73786976294838206464)), (11889/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1820571389412919/9223372036854775808), (2533901567357/4611686018427387904)), (214109/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591821000658449/1152921504606846976), (2530986312451/576460752303423488)), (107121/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192687754148567/144115188075855872), (4422674914435/144115188075855872)), (187613/144115188075855872), by norm_num⟩
  | 4 => ⟨((372200094534475/9007199254740992), (3310465280295/18014398509481984)), (35215/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485715762939091/9007199254740992), (8253315985285/9007199254740992)), (352679/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110438673915743/2251799813685248), (16438273806243/4503599627370496)), (353473/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102765225809317/1125899906842624), (3060894498325/281474976710656)), (532203/1125899906842624), by norm_num⟩
  | 0 => ⟨((269964756747511/281474976710656), (48297125239555/2251799813685248)), (2144841/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((269964756747511/281474976710656), (48297125239555/2251799813685248)), (8181919106490325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258795732642821/281474976710656), (92644268554669/2251799813685248)), (4206273/2251799813685248), by norm_num⟩
  | 2 => ⟨((1899738961025833/2251799813685248), (85179654816741/1125899906842624)), (2020209/562949953421312), by norm_num⟩
  | 3 => ⟨((1589833076592091/2251799813685248), (561422814287/4398046511104)), (1857195/281474976710656), by norm_num⟩
  | 4 => ⟨((542886309739191/1125899906842624), (405893188193155/2251799813685248)), (24772917/2251799813685248), by norm_num⟩
  | 5 => ⟨((225187180233309/1125899906842624), (782854155142079/4503599627370496)), (32820781/2251799813685248), by norm_num⟩
  | 6 => ⟨((176292429578633/18014398509481984), (78287918250541/1125899906842624)), (98156439/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-1427785471/33554432)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-364147551/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1007761118971609/18014398509481984), (649540892838161/18014398509481984)), (7512837/1125899906842624), by norm_num⟩
  | 1 => ⟨((-694466657/4294967296), (-223805267/2147483648)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((501816703/2147483648), (646880423/4294967296)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((-241739471/1073741824), (-623241635/4294967296)), (15/536870912), by norm_num⟩
  | 4 => ⟨((174679235/1073741824), (450350005/4294967296)), (11/536870912), by norm_num⟩
  | 5 => ⟨((-201955171/2147483648), (-260335787/4294967296)), (13/1073741824), by norm_num⟩
  | 6 => ⟨((778300697/17179869184), (125411201/4294967296)), (51/8589934592), by norm_num⟩
  | 7 => ⟨((-1285473345/68719476736), (-103567141/8589934592)), (171/68719476736), by norm_num⟩
  | 8 => ⟨((928873963/137438953472), (598695079/137438953472)), (125/137438953472), by norm_num⟩
  | 9 => ⟨((-1193240475/549755813888), (-48068093/34359738368)), (163/549755813888), by norm_num⟩
  | 10 => ⟨((344890857/549755813888), (444590907/1099511627776)), (3/34359738368), by norm_num⟩
  | 11 => ⟨((-362495561/2199023255552), (-58410591/549755813888)), (51/2199023255552), by norm_num⟩
  | 12 => ⟨((698497955/17592186044416), (112552215/4398046511104)), (25/4398046511104), by norm_num⟩
  | 13 => ⟨((-621205773/70368744177664), (-400391069/70368744177664)), (45/35184372088832), by norm_num⟩
  | 14 => ⟨((1026008927/562949953421312), (165325577/140737488355328)), (151/562949953421312), by norm_num⟩
  | 15 => ⟨((-395406297/1125899906842624), (-127427301/562949953421312)), (59/1125899906842624), by norm_num⟩
  | 16 => ⟨((571435597/9007199254740992), (23019517/562949953421312)), (43/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (745779433711/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777790121948159/633825300114114700748351602688), (440833046499/316912650057057350374175801344)), (92287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888641127374221/39614081257132168796771975168), (61977693863/2475880078570760549798248448)), (103829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236043466294983/309485009821345068724781056), (526664865909/1237940039285380274899124224)), (110325/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770014345129409/154742504910672534362390528), (1053002455235/154742504910672534362390528)), (27583/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387112748111405/2417851639229258349412352), (7709704783/75557863725914323419136)), (25861/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257824442577955/604462909807314587353088), (863139505757/604462909807314587353088)), (45261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886225879985797/75557863725914323419136), (700975302365/37778931862957161709568)), (18389/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296365464708911/4722366482869645213696), (131361698343/590295810358705651712)), (110347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619834911251375/590295810358705651712), (1444054095545/590295810358705651712)), (151747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821459658639843/73786976294838206464), (1803681850169/73786976294838206464)), (189715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910196085941971/4611686018427387904), (2027238450961/9223372036854775808)), (213473/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591643304710049/1152921504606846976), (2024861613405/1152921504606846976)), (213527/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298133494394275/36028797018963968), (1769083678113/144115188075855872)), (186897/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488573117083415/36028797018963968), (1324147153853/18014398509481984)), (280467/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485437618669413/9007199254740992), (3301059060111/9007199254740992)), (350799/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220338757325357/4503599627370496), (1643568656367/1125899906842624)), (175561/1125899906842624), by norm_num⟩
  | 1 => ⟨((551191617239023/562949953421312), (9792092776999/2251799813685248)), (263749/562949953421312), by norm_num⟩
  | 0 => ⟨((2158363660331803/2251799813685248), (19308639581019/2251799813685248)), (2116575/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2158363660331803/2251799813685248), (19308639581019/2251799813685248)), (8074092873580168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034319489318853/1125899906842624), (18507447131329/1125899906842624)), (4093799/2251799813685248), by norm_num⟩
  | 2 => ⟨((1899767952525433/2251799813685248), (34004111998115/1125899906842624)), (7656209/2251799813685248), by norm_num⟩
  | 3 => ⟨((200089564634329/281474976710656), (57376256837309/1125899906842624)), (3345259/562949953421312), by norm_num⟩
  | 4 => ⟨((283009752148999/562949953421312), (163146157929711/2251799813685248)), (20387917/2251799813685248), by norm_num⟩
  | 5 => ⟨((1114571233649801/4503599627370496), (20504466444637/281474976710656)), (46906707/4503599627370496), by norm_num⟩
  | 6 => ⟨((1007761118971609/18014398509481984), (649540892838161/18014398509481984)), (7512837/1125899906842624), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-364147551/8388608)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-1483837143/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1107164546295027/18014398509481984), (-270350015952015/18014398509481984)), (44271559/9007199254740992), by norm_num⟩
  | 1 => ⟨((-777239429/4294967296), (189788133/4294967296)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((1144267035/4294967296), (-69852447/1073741824)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((-280768705/1073741824), (17139689/268435456)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((826706319/4294967296), (-403734147/8589934592)), (71/4294967296), by norm_num⟩
  | 5 => ⟨((-243418631/2147483648), (928727/33554432)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((238910435/4294967296), (-233350825/17179869184)), (85/17179869184), by norm_num⟩
  | 7 => ⟨((-1607902165/68719476736), (196310647/34359738368)), (145/68719476736), by norm_num⟩
  | 8 => ⟨((295898113/34359738368), (-289012361/137438953472)), (109/137438953472), by norm_num⟩
  | 9 => ⟨((-1548895889/549755813888), (378213005/549755813888)), (145/549755813888), by norm_num⟩
  | 10 => ⟨((456062943/549755813888), (-222725023/1099511627776)), (87/1099511627776), by norm_num⟩
  | 11 => ⟨((-976617823/4398046511104), (119236407/2199023255552)), (95/4398046511104), by norm_num⟩
  | 12 => ⟨((958530529/17592186044416), (-29257027/2199023255552)), (95/17592186044416), by norm_num⟩
  | 13 => ⟨((-434205331/35184372088832), (212050537/70368744177664)), (11/8796093022208), by norm_num⟩
  | 14 => ⟨((1461132687/562949953421312), (-356782781/562949953421312)), (75/281474976710656), by norm_num⟩
  | 15 => ⟨((-573628805/1125899906842624), (140070017/1125899906842624)), (119/2251799813685248), by norm_num⟩
  | 16 => ⟨((1689015013/18014398509481984), (-206213809/9007199254740992)), (177/18014398509481984), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (-38996245297/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888856205933499/316912650057057350374175801344), (-368782366491/633825300114114700748351602688)), (92237/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888553742944463/39614081257132168796771975168), (-414781823639/39614081257132168796771975168)), (103769/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888254935615301/2475880078570760549798248448), (-440581678111/2475880078570760549798248448)), (55129/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769921607947995/154742504910672534362390528), (-440442243245/154742504910672534362390528)), (110261/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548364112461061/9671406556917033397649408), (-51595814475/1208925819614629174706176)), (103373/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628874241835937/302231454903657293676544), (-180511342109/302231454903657293676544)), (90455/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886102561198707/75557863725914323419136), (-73298059841/9444732965739290427392)), (73497/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296273075659075/4722366482869645213696), (-109886449417/1180591620717411303424)), (27563/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809854019352145/295147905179352825856), (-37748849279/36893488147419103232)), (37901/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910650655627307/36893488147419103232), (-754386648277/73786976294838206464)), (94759/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820214365130709/9223372036854775808), (-847874057273/9223372036854775808)), (213227/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591465914806089/1152921504606846976), (-846861591051/1152921504606846976)), (106625/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192379229378701/144115188075855872), (-739866496751/144115188075855872)), (46655/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488341928256299/36028797018963968), (-1107529020651/36028797018963968)), (139991/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485150260677147/9007199254740992), (-345111659971/2251799813685248)), (43759/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219768903407463/4503599627370496), (-2749035812709/4503599627370496)), (700425/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203923766349781/2251799813685248), (-511754650489/281474976710656)), (1051357/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156726109278607/2251799813685248), (-2017692037769/562949953421312)), (2105659/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2156726109278607/2251799813685248), (-2017692037769/562949953421312)), (8032451638228606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065637604584887/2251799813685248), (-15460021168465/2251799813685248)), (2024303/1125899906842624), by norm_num⟩
  | 2 => ⟨((1894759771845793/2251799813685248), (-28363801168449/2251799813685248)), (1870847/562949953421312), by norm_num⟩
  | 3 => ⟨((1593973880792809/2251799813685248), (-1491656504721/70368744177664)), (12782203/2251799813685248), by norm_num⟩
  | 4 => ⟨((281827260704419/562949953421312), (-4223575280875/140737488355328)), (18638097/2251799813685248), by norm_num⟩
  | 5 => ⟨((281165979265925/1125899906842624), (-16915445425353/562949953421312)), (39560189/4503599627370496), by norm_num⟩
  | 6 => ⟨((1107164546295027/18014398509481984), (-270350015952015/18014398509481984)), (44271559/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-1483837143/33554432)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-1509686175/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((577831175870607/18014398509481984), (-919734119456843/18014398509481984)), (35336197/4503599627370496), by norm_num⟩
  | 1 => ⟨((-825418235/8589934592), (1313818543/8589934592)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((154545753/1073741824), (-983962153/4294967296)), (155/4294967296), by norm_num⟩
  | 3 => ⟨((-38581475/268435456), (982562393/4294967296)), (157/4294967296), by norm_num⟩
  | 4 => ⟨((462319079/4294967296), (-183968367/1073741824)), (119/4294967296), by norm_num⟩
  | 5 => ⟨((-276996837/4294967296), (881791959/8589934592)), (9/536870912), by norm_num⟩
  | 6 => ⟨((69150697/2147483648), (-880537543/17179869184)), (73/8589934592), by norm_num⟩
  | 7 => ⟨((-473501657/34359738368), (376836391/17179869184)), (127/34359738368), by norm_num⟩
  | 8 => ⟨((354621049/68719476736), (-1128900939/137438953472)), (193/137438953472), by norm_num⟩
  | 9 => ⟨((-59019429/34359738368), (751529995/274877906944)), (65/137438953472), by norm_num⟩
  | 10 => ⟨((282890253/549755813888), (-112569133/137438953472)), (79/549755813888), by norm_num⟩
  | 11 => ⟨((-308168531/2199023255552), (245255989/1099511627776)), (87/2199023255552), by norm_num⟩
  | 12 => ⟨((153865069/4398046511104), (-979628375/17592186044416)), (11/1099511627776), by norm_num⟩
  | 13 => ⟨((-141827247/17592186044416), (902985951/70368744177664)), (41/17592186044416), by norm_num⟩
  | 14 => ⟨((242786549/140737488355328), (-386443451/140737488355328)), (71/140737488355328), by norm_num⟩
  | 15 => ⟨((-387905867/1125899906842624), (1234859859/2251799813685248)), (229/2251799813685248), by norm_num⟩
  | 16 => ⟨((581031063/9007199254740992), (-924827383/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (-164431427151/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888818572013133/316912650057057350374175801344), (-1554882846995/633825300114114700748351602688)), (46177/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888469020089285/39614081257132168796771975168), (-874410313547/19807040628566084398385987584)), (25977/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888164853035147/2475880078570760549798248448), (-1857589831489/2475880078570760549798248448)), (110413/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769831452867151/154742504910672534362390528), (-1856991546905/154742504910672534362390528)), (110427/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774139757560059/4835703278458516698824704), (-870147079473/4835703278458516698824704)), (51769/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157209298016911/75557863725914323419136), (-761061133329/302231454903657293676544)), (45305/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885982005522923/75557863725914323419136), (-2472258452905/75557863725914323419136)), (147267/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296182533154103/4722366482869645213696), (-1853153011821/4722366482869645213696)), (110473/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809791669387163/295147905179352825856), (-2546395214751/590295810358705651712)), (1187/4611686018427387904), by norm_num⟩
  | 8 => ⟨((910572565492159/36893488147419103232), (-795115199367/18446744073709551616)), (189975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820038243466571/9223372036854775808), (-3574538536553/9223372036854775808)), (213797/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397822317768681/288230376151711744), (-3570193683071/1152921504606846976)), (53473/288230376151711744), by norm_num⟩
  | 5 => ⟨((596112040428575/72057594037927936), (-3119038341123/144115188075855872)), (93631/72057594037927936), by norm_num⟩
  | 4 => ⟨((744054020060283/18014398509481984), (-2334406147651/18014398509481984)), (281107/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484855872713601/9007199254740992), (-5818999527645/9007199254740992)), (175879/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219174090222567/4503599627370496), (-11587104340197/4503599627370496)), (176161/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101508307039331/1125899906842624), (-17253953031267/2251799813685248)), (132475/281474976710656), by norm_num⟩
  | 0 => ⟨((2154853032428989/2251799813685248), (-34004279838031/2251799813685248)), (2131019/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2154853032428989/2251799813685248), (-34004279838031/2251799813685248)), (8129192360884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515391651614417/562949953421312), (-65080585831141/2251799813685248)), (2071453/1125899906842624), by norm_num⟩
  | 2 => ⟨((1885523466342525/2251799813685248), (-59582544444129/1125899906842624)), (489081/140737488355328), by norm_num⟩
  | 3 => ⟨((1572519192069503/2251799813685248), (-199563540330775/2251799813685248)), (6966553/1125899906842624), by norm_num⟩
  | 4 => ⟨((270116263001171/562949953421312), (-69681482185997/562949953421312)), (10964837/1125899906842624), by norm_num⟩
  | 5 => ⟨((967862754607727/4503599627370496), (-66869537706055/562949953421312)), (26473593/2251799813685248), by norm_num⟩
  | 6 => ⟨((577831175870607/18014398509481984), (-919734119456843/18014398509481984)), (35336197/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1509686175/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-1534273765/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-693032660573/70368744177664), (-511170926656459/9007199254740992)), (22111609/2251799813685248), by norm_num⟩
  | 1 => ⟨((257562681/8589934592), (742088011/4294967296)), (259/8589934592), by norm_num⟩
  | 2 => ⟨((-24504855/536870912), (-141206475/536870912)), (199/4294967296), by norm_num⟩
  | 3 => ⟨((24868527/536870912), (1146416751/4294967296)), (51/1073741824), by norm_num⟩
  | 4 => ⟨((-151425577/4294967296), (-1745145761/8589934592)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((184407427/8589934592), (1062627085/8589934592)), (3/134217728), by norm_num⟩
  | 6 => ⟨((-187144183/17179869184), (-1078397335/17179869184)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((10174369/2147483648), (469029269/17179869184)), (173/34359738368), by norm_num⟩
  | 8 => ⟨((-123904379/68719476736), (-713985067/68719476736)), (133/68719476736), by norm_num⟩
  | 9 => ⟨((41914407/68719476736), (120763531/34359738368)), (91/137438953472), by norm_num⟩
  | 10 => ⟨((-51043741/274877906944), (-4595841/4294967296)), (7/34359738368), by norm_num⟩
  | 11 => ⟨((28255239/549755813888), (651270565/2199023255552)), (125/2199023255552), by norm_num⟩
  | 12 => ⟨((-114698279/8796093022208), (-1321871899/17592186044416)), (255/17592186044416), by norm_num⟩
  | 13 => ⟨((214893221/70368744177664), (19348407/1099511627776)), (241/70368744177664), by norm_num⟩
  | 14 => ⟨((-186927781/281474976710656), (-1077150341/281474976710656)), (211/281474976710656), by norm_num⟩
  | 15 => ⟨((151761553/1125899906842624), (437254451/562949953421312)), (43/281474976710656), by norm_num⟩
  | 16 => ⟨((-231020727/9007199254740992), (-1331230987/9007199254740992)), (33/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (-1134981309201/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777564153629509/633825300114114700748351602688), (-2682926278041/633825300114114700748351602688)), (92465/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944193393195895/19807040628566084398385987584), (-1508773750547/19807040628566084398385987584)), (13005/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472019329047339/618970019642690137449562112), (-3205210699677/2475880078570760549798248448)), (110563/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769743732294989/154742504910672534362390528), (-3204160967215/154742504910672534362390528)), (13823/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548197082059587/9671406556917033397649408), (-3002785992833/9671406556917033397649408)), (6481/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((157200257548965/75557863725914323419136), (-1313161654981/302231454903657293676544)), (45379/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117866507162695/4722366482869645213696), (-1066421708825/18889465931478580854784)), (73763/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648046898087323/2361183241434822606848), (-3197438670453/4722366482869645213696)), (110683/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619460808222975/590295810358705651712), (-1098378022819/147573952589676412928)), (38063/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820991193436383/73786976294838206464), (-2743722167213/36893488147419103232)), (190409/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909932000665919/4611686018427387904), (-770908419357/1152921504606846976)), (214341/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397778426116901/288230376151711744), (-6159641084965/1152921504606846976)), (214503/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298017243718543/36028797018963968), (-5381117566123/144115188075855872)), (93937/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487872422789051/36028797018963968), (-8054567476215/36028797018963968)), (141089/18014398509481984), by norm_num⟩
  | 3 => ⟨((742278100476325/4503599627370496), (-10038331488467/9007199254740992)), (176683/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109279702071899/2251799813685248), (-19987279643423/4503599627370496)), (354333/2251799813685248), by norm_num⟩
  | 1 => ⟨((550514150981645/562949953421312), (-29758334952701/2251799813685248)), (66741/140737488355328), by norm_num⟩
  | 0 => ⟨((2152783326532991/2251799813685248), (-14657889686065/562949953421312)), (269405/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2152783326532991/2251799813685248), (-14657889686065/562949953421312)), (1027698517919444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2056594179985569/2251799813685248), (-112106805681551/2251799813685248)), (4233175/2251799813685248), by norm_num⟩
  | 2 => ⟨((936364693620105/1125899906842624), (-102388410683863/1125899906842624)), (8153915/2251799813685248), by norm_num⟩
  | 3 => ⟨((1538849852550871/2251799813685248), (-85152234419401/562949953421312)), (15045573/2251799813685248), by norm_num⟩
  | 4 => ⟨((500054313572467/1125899906842624), (-465535177982703/2251799813685248)), (3139437/281474976710656), by norm_num⟩
  | 5 => ⟨((695882697377159/4503599627370496), (-413523213662573/2251799813685248)), (16347089/1125899906842624), by norm_num⟩
  | 6 => ⟨((-693032660573/70368744177664), (-511170926656459/9007199254740992)), (22111609/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-1534273765/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile002Terms2

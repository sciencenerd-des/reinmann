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
namespace Reinmann.XiBand97.Tile015Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26461/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26461/1280))
  have he : value ((69/80), (26461/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1524125127/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((176338209978077/9007199254740992), (-1342269917798855/9007199254740992)), (26031141/1125899906842624), by norm_num⟩
  | 1 => ⟨((-92376387/2147483648), (351580197/1073741824)), (55/1073741824), by norm_num⟩
  | 2 => ⟨((50742917/1073741824), (-386250325/1073741824)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((-148658113/4294967296), (565785805/2147483648)), (181/4294967296), by norm_num⟩
  | 4 => ⟨((81658815/4294967296), (-1243158477/8589934592)), (201/8589934592), by norm_num⟩
  | 5 => ⟨((-35884551/4294967296), (68287459/1073741824)), (179/17179869184), by norm_num⟩
  | 6 => ⟨((210257113/68719476736), (-800228711/34359738368)), (265/68719476736), by norm_num⟩
  | 7 => ⟨((-131994885/137438953472), (1004732681/137438953472)), (21/17179869184), by norm_num⟩
  | 8 => ⟨((145011203/549755813888), (-551905835/274877906944)), (187/549755813888), by norm_num⟩
  | 9 => ⟨((-141609857/2199023255552), (1077920947/2199023255552)), (185/2199023255552), by norm_num⟩
  | 10 => ⟨((248918927/17592186044416), (-947373759/8796093022208)), (41/2199023255552), by norm_num⟩
  | 11 => ⟨((-99441961/35184372088832), (1513885751/70368744177664)), (265/70368744177664), by norm_num⟩
  | 12 => ⟨((72832107/140737488355328), (-1108782327/281474976710656)), (49/70368744177664), by norm_num⟩
  | 13 => ⟨((-49239537/562949953421312), (749613471/1125899906842624)), (67/562949953421312), by norm_num⟩
  | 14 => ⟨((123646081/9007199254740992), (-941182367/9007199254740992)), (339/18014398509481984), by norm_num⟩
  | 15 => ⟨((-36223761/18014398509481984), (551463741/36028797018963968)), (201/72057594037927936), by norm_num⟩
  | 16 => ⟨((39795869/144115188075855872), (-605844843/288230376151711744)), (223/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1875983840983/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779043220616721/633825300114114700748351602688), (-2220787083431/633825300114114700748351602688)), (92419/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890050453898663/39614081257132168796771975168), (-1248983525595/19807040628566084398385987584)), (103985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944922312065417/1237940039285380274899124224), (-2653576562665/2475880078570760549798248448)), (110501/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771510659073571/154742504910672534362390528), (-2652999095221/154742504910672534362390528)), (55259/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549853170956285/9671406556917033397649408), (-2486573236553/9671406556917033397649408)), (103631/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629525366624303/302231454903657293676544), (-1087569164331/302231454903657293676544)), (90697/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472054362205269/18889465931478580854784), (-3533450278057/75557863725914323419136)), (73709/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297858132625649/4722366482869645213696), (-2649082234655/4722366482869645213696)), (27649/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810942845810283/295147905179352825856), (-3640854822189/590295810358705651712)), (19015/73786976294838206464), by norm_num⟩
  | 8 => ⟨((456005169766301/18446744073709551616), (-4548619779771/73786976294838206464)), (47557/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823269947416367/9223372036854775808), (-5113832055717/9223372036854775808)), (214113/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199314608690413/144115188075855872), (-1277407076713/288230376151711744)), (26781/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195043616375379/144115188075855872), (-4466199326075/144115188075855872)), (93809/72057594037927936), by norm_num⟩
  | 4 => ⟨((746164065523591/18014398509481984), (-1672464384135/9007199254740992)), (2201/281474976710656), by norm_num⟩
  | 3 => ⟨((1490114895990697/9007199254740992), (-8345820586537/9007199254740992)), (22043/562949953421312), by norm_num⟩
  | 2 => ⟨((557410997594047/1125899906842624), (-16642221928377/4503599627370496)), (353483/2251799813685248), by norm_num⟩
  | 1 => ⟨((277325191758127/281474976710656), (-24840081100915/2251799813685248)), (1064431/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185545759231315/2251799813685248), (-49188930299405/2251799813685248)), (268105/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185545759231315/2251799813685248), (-49188930299405/2251799813685248)), (1022739411474132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1060083291111177/1125899906842624), (-23870829316983/562949953421312)), (1064293/562949953421312), by norm_num⟩
  | 2 => ⟨((996089715709287/1125899906842624), (-179803317507069/2251799813685248)), (4188829/1125899906842624), by norm_num⟩
  | 3 => ⟨((1748134816450835/2251799813685248), (-39768241015637/281474976710656)), (8080705/1125899906842624), by norm_num⟩
  | 4 => ⟨((1312176369741021/2251799813685248), (-493971062869343/2251799813685248)), (463435/35184372088832), by norm_num⟩
  | 5 => ⟨((164068693559389/562949953421312), (-575696962131119/2251799813685248)), (23789879/1125899906842624), by norm_num⟩
  | 6 => ⟨((176338209978077/9007199254740992), (-1342269917798855/9007199254740992)), (26031141/1125899906842624), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1524125127/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-798604711/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-549203037210195/4503599627370496), (567187605257613/9007199254740992)), (221192539/9007199254740992), by norm_num⟩
  | 1 => ⟨((603001941/2147483648), (-155687061/1073741824)), (245/4294967296), by norm_num⟩
  | 2 => ⟨((-1388463281/4294967296), (179241353/1073741824)), (285/4294967296), by norm_num⟩
  | 3 => ⟨((1065684951/4294967296), (-275145645/2147483648)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-1226915141/8589934592), (633546261/8589934592)), (257/8589934592), by norm_num⟩
  | 5 => ⟨((565015303/8589934592), (-583517671/17179869184)), (239/17179869184), by norm_num⟩
  | 6 => ⟨((-867330543/34359738368), (111966591/8589934592)), (93/17179869184), by norm_num⟩
  | 7 => ⟨((71325085/8589934592), (-589285951/137438953472)), (247/137438953472), by norm_num⟩
  | 8 => ⟨((-328464155/137438953472), (678440523/549755813888)), (287/549755813888), by norm_num⟩
  | 9 => ⟨((336140741/549755813888), (-173574115/549755813888)), (37/274877906944), by norm_num⟩
  | 10 => ⟨((-1238388255/8796093022208), (39966917/549755813888)), (275/8796093022208), by norm_num⟩
  | 11 => ⟨((1036907031/35184372088832), (-535431141/35184372088832)), (29/4398046511104), by norm_num⟩
  | 12 => ⟨((-397927779/70368744177664), (102739647/35184372088832)), (45/35184372088832), by norm_num⟩
  | 13 => ⟨((1127707781/1125899906842624), (-582318227/1125899906842624)), (257/1125899906842624), by norm_num⟩
  | 14 => ⟨((-185474509/1125899906842624), (383096363/4503599627370496)), (171/4503599627370496), by norm_num⟩
  | 15 => ⟨((455542229/18014398509481984), (-58807465/4503599627370496)), (53/9007199254740992), by norm_num⟩
  | 16 => ⟨((-524462373/144115188075855872), (541636769/288230376151711744)), (123/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (867842979281/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778896705811061/633825300114114700748351602688), (4108789163357/633825300114114700748351602688)), (92605/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889885289688467/39614081257132168796771975168), (2310780953773/19807040628566084398385987584)), (52103/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889668700261477/2475880078570760549798248448), (2454706105419/1237940039285380274899124224)), (110749/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771334244067189/154742504910672534362390528), (4908290276255/154742504910672534362390528)), (110783/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387421815098139/2417851639229258349412352), (4600330226075/9671406556917033397649408)), (103895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258905040389981/604462909807314587353088), (251506075349/37778931862957161709568)), (1421/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((943989860820719/37778931862957161709568), (6536923794745/75557863725914323419136)), (36963/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297678983798677/4722366482869645213696), (4900738304937/4722366482869645213696)), (27737/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202704747081427/73786976294838206464), (420958731367/36893488147419103232)), (152649/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455927239999859/18446744073709551616), (525900786617/4611686018427387904)), (190955/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455729103537115/2305843009213693952), (591229264937/576460752303423488)), (215023/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594159781041725/1152921504606846976), (2362872168379/288230376151711744)), (215271/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194727173178659/144115188075855872), (4130427241409/72057594037927936)), (188641/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491845506777379/36028797018963968), (6186447646869/18014398509481984)), (283521/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489497736177135/9007199254740992), (15433964931825/9007199254740992)), (88845/2251799813685248), by norm_num⟩
  | 2 => ⟨((278546028800705/562949953421312), (3846444483149/562949953421312)), (356851/2251799813685248), by norm_num⟩
  | 1 => ⟨((554146246263465/562949953421312), (22958355016355/1125899906842624)), (134741/281474976710656), by norm_num⟩
  | 0 => ⟨((34079768184889/35184372088832), (45436401286191/1125899906842624)), (1092727/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((34079768184889/35184372088832), (45436401286191/1125899906842624)), (4168422703269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527240681053161/562949953421312), (88019875362817/1125899906842624)), (1102519/562949953421312), by norm_num⟩
  | 2 => ⟨((980711906857861/1125899906842624), (82436562522947/562949953421312)), (139847/35184372088832), by norm_num⟩
  | 3 => ⟨((1660205656311545/2251799813685248), (574449063795773/2251799813685248)), (9106693/1125899906842624), by norm_num⟩
  | 4 => ⟨((1077489694957471/2251799813685248), (847058942966873/2251799813685248)), (36149421/2251799813685248), by norm_num⟩
  | 5 => ⟨((49235636665411/562949953421312), (1621276059304175/4503599627370496)), (123583491/4503599627370496), by norm_num⟩
  | 6 => ⟨((-549203037210195/4503599627370496), (567187605257613/9007199254740992)), (221192539/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-798604711/16777216)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1663322209/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((218704910815159/2251799813685248), (182209431909141/2251799813685248)), (122483555/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1000273651/4294967296), (-208339279/1073741824)), (143/4294967296), by norm_num⟩
  | 2 => ⟨((599637865/2147483648), (124893943/536870912)), (11/268435456), by norm_num⟩
  | 3 => ⟨((-958579201/4294967296), (-798620255/4294967296)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((1149286267/8589934592), (957503867/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-1102347243/17179869184), (-918397599/17179869184)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((440552207/17179869184), (367036877/17179869184)), (69/17179869184), by norm_num⟩
  | 7 => ⟨((-603656031/68719476736), (-15716357/2147483648)), (3/2147483648), by norm_num⟩
  | 8 => ⟨((180937993/68719476736), (602978851/274877906944)), (59/137438953472), by norm_num⟩
  | 9 => ⟨((-771325081/1099511627776), (-321306697/549755813888)), (127/1099511627776), by norm_num⟩
  | 10 => ⟨((369911353/2199023255552), (77045981/549755813888)), (31/1099511627776), by norm_num⟩
  | 11 => ⟨((-645097225/17592186044416), (-537449291/17592186044416)), (55/8796093022208), by norm_num⟩
  | 12 => ⟨((1031250391/140737488355328), (859164743/140737488355328)), (89/70368744177664), by norm_num⟩
  | 13 => ⟨((-95108863/70368744177664), (-158475929/140737488355328)), (133/562949953421312), by norm_num⟩
  | 14 => ⟨((1042564997/4503599627370496), (868591271/4503599627370496)), (185/4503599627370496), by norm_num⟩
  | 15 => ⟨((-666656447/18014398509481984), (-555410907/18014398509481984)), (121/18014398509481984), by norm_num⟩
  | 16 => ⟨((799286171/144115188075855872), (332954297/72057594037927936)), (147/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (904817174117/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444694597796239/158456325028528675187087900672), (1070815454787/633825300114114700748351602688)), (46153/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889752688401225/39614081257132168796771975168), (1204449609459/39614081257132168796771975168)), (103851/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944764230838629/1237940039285380274899124224), (39983054707/77371252455336267181195264)), (110349/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885597368268671/77371252455336267181195264), (1279154154383/154742504910672534362390528)), (55179/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549557248366865/9671406556917033397649408), (1198884546925/9671406556917033397649408)), (51735/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258792055631763/604462909807314587353088), (1048701616239/604462909807314587353088)), (45273/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887797574864317/75557863725914323419136), (212941991467/9444732965739290427392)), (73577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297543644386449/4722366482869645213696), (319280878269/1180591620717411303424)), (110381/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810726973866629/295147905179352825856), (1755186562071/590295810358705651712)), (151799/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823482014398745/73786976294838206464), (2192696568923/73786976294838206464)), (189787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822665343982009/9223372036854775808), (2465015767467/9223372036854775808)), (213561/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398478501655907/288230376151711744), (615701949601/288230376151711744)), (106813/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194518066198843/144115188075855872), (1076237714803/72057594037927936)), (46749/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491543707412379/36028797018963968), (1611878388727/18014398509481984)), (280641/36028797018963968), by norm_num⟩
  | 3 => ⟨((93071323507727/562949953421312), (1005259189469/2251799813685248)), (175529/4503599627370496), by norm_num⟩
  | 2 => ⟨((556929226778599/1125899906842624), (4008076745709/2251799813685248)), (351443/2251799813685248), by norm_num⟩
  | 1 => ⟨((553940386766367/562949953421312), (11959631408751/2251799813685248)), (1056267/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180066822362311/2251799813685248), (23662071475469/2251799813685248)), (1060163/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180066822362311/2251799813685248), (23662071475469/2251799813685248)), (4044200901511764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2110370303548945/2251799813685248), (5727074034127/281474976710656)), (4150125/2251799813685248), by norm_num⟩
  | 2 => ⟨((1976891387466819/2251799813685248), (21469487464017/562949953421312)), (7947817/2251799813685248), by norm_num⟩
  | 3 => ⟨((1732269676843591/2251799813685248), (37696818876169/562949953421312)), (7280627/1125899906842624), by norm_num⟩
  | 4 => ⟨((661253592073069/1125899906842624), (28999494473615/281474976710656)), (24353561/2251799813685248), by norm_num⟩
  | 5 => ⟨((1505642835844629/4503599627370496), (545015265316267/4503599627370496)), (67248763/4503599627370496), by norm_num⟩
  | 6 => ⟨((218704910815159/2251799813685248), (182209431909141/2251799813685248)), (122483555/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1663322209/33554432)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-861839227/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((475243041573199/9007199254740992), (-471687996373505/4503599627370496)), (4449527/281474976710656), by norm_num⟩
  | 1 => ⟨((-70389187/536870912), (1117802275/4294967296)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((699642235/4294967296), (-1388817153/4294967296)), (215/4294967296), by norm_num⟩
  | 3 => ⟨((-289757607/2147483648), (575180163/2147483648)), (45/1073741824), by norm_num⟩
  | 4 => ⟨((180005151/2147483648), (-357317253/2147483648)), (57/2147483648), by norm_num⟩
  | 5 => ⟨((-715673595/17179869184), (1420640029/17179869184)), (115/8589934592), by norm_num⟩
  | 6 => ⟨((592794025/34359738368), (-1176719285/34359738368)), (193/34359738368), by norm_num⟩
  | 7 => ⟨((-420867947/68719476736), (835439307/68719476736)), (139/68719476736), by norm_num⟩
  | 8 => ⟨((130727195/68719476736), (-129749293/34359738368)), (175/274877906944), by norm_num⟩
  | 9 => ⟨((-288751001/549755813888), (1146364021/1099511627776)), (195/1099511627776), by norm_num⟩
  | 10 => ⟨((287007713/2199023255552), (-1139443031/4398046511104)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((-518681727/17592186044416), (514801739/8796093022208)), (179/17592186044416), by norm_num⟩
  | 12 => ⟨((53703153/8796093022208), (-852822843/70368744177664)), (75/35184372088832), by norm_num⟩
  | 13 => ⟨((-656971431/562949953421312), (326028485/140737488355328)), (29/70368744177664), by norm_num⟩
  | 14 => ⟨((466432193/2251799813685248), (-925886115/2251799813685248)), (167/2251799813685248), by norm_num⟩
  | 15 => ⟨((-618154911/18014398509481984), (613530817/9007199254740992)), (223/18014398509481984), by norm_num⟩
  | 16 => ⟨((48001789/9007199254740992), (-762283403/72057594037927936)), (35/18014398509481984), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-22472870341/158456325028528675187087900672)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111166360571513/39614081257132168796771975168), (-850958787047/316912650057057350374175801344)), (5773/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889621459946147/39614081257132168796771975168), (-119643638407/2475880078570760549798248448)), (103925/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472347248078249/618970019642690137449562112), (-1016748564265/1237940039285380274899124224)), (3451/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771055223207911/154742504910672534362390528), (-1016498492295/77371252455336267181195264)), (55223/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193678300993915/1208925819614629174706176), (-952701714499/4835703278458516698824704)), (103559/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258677523648255/604462909807314587353088), (-833348467533/302231454903657293676544)), (22657/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943805686541737/37778931862957161709568), (-2707387151737/75557863725914323419136)), (147299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81087744797577/295147905179352825856), (-2029669796581/4722366482869645213696)), (110499/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101328856154623/36893488147419103232), (-2789382009907/590295810358705651712)), (18997/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455810379376323/18446744073709551616), (-871151954003/18446744073709551616)), (190029/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911197265359421/4611686018427387904), (-3917271231149/9223372036854775808)), (213865/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593642876370891/1152921504606846976), (-1956816778847/576460752303423488)), (13373/72057594037927936), by norm_num⟩
  | 5 => ⟨((597140235878975/72057594037927936), (-1710170570819/72057594037927936)), (93669/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491186607664891/36028797018963968), (-5122345662789/36028797018963968)), (281239/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488693568693599/9007199254740992), (-3194332423895/4503599627370496)), (351955/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226818019563037/4503599627370496), (-6367310644087/2251799813685248)), (176283/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107202061542633/1125899906842624), (-18995486779985/2251799813685248)), (1060763/2251799813685248), by norm_num⟩
  | 0 => ⟨((272164516945933/281474976710656), (-18783571557359/1125899906842624)), (133365/140737488355328), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((272164516945933/281474976710656), (-18783571557359/1125899906842624)), (508747101366949037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((526167361232303/562949953421312), (-72649039558257/2251799813685248)), (4197715/2251799813685248), by norm_num⟩
  | 2 => ⟨((491202144455849/562949953421312), (-135804446587533/2251799813685248)), (8117741/2251799813685248), by norm_num⟩
  | 3 => ⟨((1706204022411595/2251799813685248), (-236992418189303/2251799813685248)), (7572713/1125899906842624), by norm_num⟩
  | 4 => ⟨((1267859932514123/2251799813685248), (-359141531798847/2251799813685248)), (13069785/1125899906842624), by norm_num⟩
  | 5 => ⟨((1313159508786205/4503599627370496), (-808848380752467/4503599627370496)), (18886723/1125899906842624), by norm_num⟩
  | 6 => ⟨((475243041573199/9007199254740992), (-471687996373505/4503599627370496)), (4449527/281474976710656), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-861839227/16777216)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-889600409/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-457258808754271/4503599627370496), (-184099301955149/4503599627370496)), (10926027/562949953421312), by norm_num⟩
  | 1 => ⟨((559256405/2147483648), (450330149/4294967296)), (27/536870912), by norm_num⟩
  | 2 => ⟨((-1434464357/4294967296), (-577537013/4294967296)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((613221405/2147483648), (493784397/4294967296)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-196610231/1073741824), (-316632993/4294967296)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((806872457/8589934592), (324859037/8589934592)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((-344931165/8589934592), (-277748993/17179869184)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((1011121109/68719476736), (407092629/68719476736)), (207/68719476736), by norm_num⟩
  | 8 => ⟨((-324184305/68719476736), (-522085989/274877906944)), (67/68719476736), by norm_num⟩
  | 9 => ⟨((369562811/274877906944), (595166277/1099511627776)), (77/274877906944), by norm_num⟩
  | 10 => ⟨((-189581979/549755813888), (-9541071/68719476736)), (159/2199023255552), by norm_num⟩
  | 11 => ⟨((176824791/2199023255552), (142384663/4398046511104)), (299/17592186044416), by norm_num⟩
  | 12 => ⟨((-1209457691/70368744177664), (-486945933/70368744177664)), (129/35184372088832), by norm_num⟩
  | 13 => ⟨((477261189/140737488355328), (192152563/140737488355328)), (103/140737488355328), by norm_num⟩
  | 14 => ⟨((-1399029463/2251799813685248), (-70408799/281474976710656)), (19/140737488355328), by norm_num⟩
  | 15 => ⟨((956917259/9007199254740992), (385269341/9007199254740992)), (105/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1227222155/72057594037927936), (-247049087/36028797018963968)), (17/4503599627370496), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-3593689197155/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889273615357869/316912650057057350374175801344), (-4251978174369/633825300114114700748351602688)), (92619/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889492171714229/39614081257132168796771975168), (-4782529196565/39614081257132168796771975168)), (104223/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944625527391833/1237940039285380274899124224), (-2540143965577/1237940039285380274899124224)), (6923/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770916646351061/154742504910672534362390528), (-5078995036689/154742504910672534362390528)), (110803/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774647906669631/4835703278458516698824704), (-4760184373765/9671406556917033397649408)), (103915/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258562575090107/604462909807314587353088), (-2081894054529/302231454903657293676544)), (90963/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235927913881771/9444732965739290427392), (-6763581435955/75557863725914323419136)), (147885/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648630879791455/2361183241434822606848), (-2535217079313/2361183241434822606848)), (110975/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101316526854375/36893488147419103232), (-3484094309571/295147905179352825856)), (76345/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822992231204405/73786976294838206464), (-136011719279/1152921504606846976)), (191011/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822110376779335/9223372036854775808), (-9785303795913/9223372036854775808)), (107547/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796677048971417/576460752303423488), (-610992697535/72057594037927936)), (107675/576460752303423488), by norm_num⟩
  | 5 => ⟨((597011300274091/72057594037927936), (-4271652772761/72057594037927936)), (11795/9007199254740992), by norm_num⟩
  | 4 => ⟨((186348681474847/4503599627370496), (-799611805367/2251799813685248)), (70915/9007199254740992), by norm_num⟩
  | 3 => ⟨((744089541461515/4503599627370496), (-7977611711873/4503599627370496)), (355589/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112867602119551/2251799813685248), (-15899772184433/2251799813685248)), (178557/1125899906842624), by norm_num⟩
  | 1 => ⟨((276580783081613/281474976710656), (-11855634027599/562949953421312)), (269747/562949953421312), by norm_num⟩
  | 0 => ⟨((1086635850104155/1125899906842624), (-46870407453621/1125899906842624)), (273583/281474976710656), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086635850104155/1125899906842624), (-46870407453621/1125899906842624)), (1043636323095226199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1046789886448983/1125899906842624), (-11308968217015/140737488355328)), (2203451/1125899906842624), by norm_num⟩
  | 2 => ⟨((241492143969809/281474976710656), (-168229711842745/1125899906842624)), (2225687/562949953421312), by norm_num⟩
  | 3 => ⟨((1607237105431143/2251799813685248), (-577332369180221/2251799813685248)), (17936731/2251799813685248), by norm_num⟩
  | 4 => ⟨((999155624268969/2251799813685248), (-824149642675673/2251799813685248)), (34802415/2251799813685248), by norm_num⟩
  | 5 => ⟨((70852063768417/1125899906842624), (-22855432844045/70368744177664)), (112719483/4503599627370496), by norm_num⟩
  | 6 => ⟨((-457258808754271/4503599627370496), (-184099301955149/4503599627370496)), (10926027/562949953421312), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-889600409/16777216)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1830606497/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-23650497269277/562949953421312), (843853149838937/9007199254740992)), (81946555/4503599627370496), by norm_num⟩
  | 1 => ⟨((238094399/2147483648), (-265476327/1073741824)), (13/268435456), by norm_num⟩
  | 2 => ⟨((-628344769/4294967296), (1401214493/4294967296)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((138186489/1073741824), (-1232628459/4294967296)), (123/2147483648), by norm_num⟩
  | 4 => ⟨((-364682067/4294967296), (203311073/1073741824)), (41/1073741824), by norm_num⟩
  | 5 => ⟨((384966753/8589934592), (-214619831/2147483648)), (175/8589934592), by norm_num⟩
  | 6 => ⟨((-338649777/17179869184), (755192051/17179869184)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((255347479/34359738368), (-1138854353/68719476736)), (119/34359738368), by norm_num⟩
  | 8 => ⟨((-168469159/68719476736), (375687741/68719476736)), (159/137438953472), by norm_num⟩
  | 9 => ⟨((197599897/274877906944), (-881299099/549755813888)), (47/137438953472), by norm_num⟩
  | 10 => ⟨((-417181965/2199023255552), (465159769/1099511627776)), (25/274877906944), by norm_num⟩
  | 11 => ⟨((400351681/8796093022208), (-892787853/8796093022208)), (97/4398046511104), by norm_num⟩
  | 12 => ⟨((-352183679/35184372088832), (98171597/4398046511104)), (173/35184372088832), by norm_num⟩
  | 13 => ⟨((8936855/4398046511104), (-159434137/35184372088832)), (71/70368744177664), by norm_num⟩
  | 14 => ⟨((-431266243/1125899906842624), (480863803/562949953421312)), (27/140737488355328), by norm_num⟩
  | 15 => ⟨((18968939/281474976710656), (-1353628953/9007199254740992)), (153/4503599627370496), by norm_num⟩
  | 16 => ⟨((-100120235/9007199254740992), (446538051/18014398509481984)), (51/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (2595248911983/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889226678216265/316912650057057350374175801344), (1535160221483/316912650057057350374175801344)), (92503/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889386845212393/39614081257132168796771975168), (3453418040879/39614081257132168796771975168)), (104085/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472284878143811/618970019642690137449562112), (1834201956591/1237940039285380274899124224)), (110613/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221350689617097/19342813113834066795298816), (1833722406089/77371252455336267181195264)), (55319/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549192067827861/9671406556917033397649408), (3437210731833/9671406556917033397649408)), (51875/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258472235768159/604462909807314587353088), (3006540908989/604462909807314587353088)), (11351/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887277330240071/75557863725914323419136), (4883719958173/75557863725914323419136)), (147613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297152991316769/4722366482869645213696), (915280052645/1180591620717411303424)), (55377/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405229009434861/147573952589676412928), (2515664060169/295147905179352825856)), (152359/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822808485759231/73786976294838206464), (6285093974491/73786976294838206464)), (47639/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821906058248633/9223372036854775808), (3532571552555/4611686018427387904)), (53631/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593152767962471/1152921504606846976), (7058163646951/1152921504606846976)), (107355/576460752303423488), by norm_num⟩
  | 5 => ⟨((298462447907017/36028797018963968), (6168048258593/144115188075855872)), (11755/9007199254740992), by norm_num⟩
  | 4 => ⟨((186317116224717/4503599627370496), (9236399910485/36028797018963968)), (141269/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487875099335541/9007199254740992), (11518112154631/9007199254740992)), (353905/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225162080079407/4503599627370496), (22954217416213/4503599627370496)), (710013/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105936557068779/1125899906842624), (34226855513537/2251799813685248)), (1070539/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172068121022427/2251799813685248), (33819552334273/1125899906842624)), (2163245/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172068121022427/2251799813685248), (33819552334273/1125899906842624)), (8252124794966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093127837224499/2251799813685248), (130488280611949/2251799813685248)), (4303257/2251799813685248), by norm_num⟩
  | 2 => ⟨((1938075012291949/2251799813685248), (242586975023713/2251799813685248)), (8498795/2251799813685248), by norm_num⟩
  | 3 => ⟨((1641924957249367/2251799813685248), (52197330302589/281474976710656)), (16460611/2251799813685248), by norm_num⟩
  | 4 => ⟨((139973901504687/281474976710656), (152241063001685/562949953421312)), (30109861/2251799813685248), by norm_num⟩
  | 5 => ⟨((196086457811945/1125899906842624), (1211320497848573/4503599627370496)), (46231985/2251799813685248), by norm_num⟩
  | 6 => ⟨((-23650497269277/562949953421312), (843853149838937/9007199254740992)), (81946555/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1830606497/33554432)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-234808005/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((735460660453423/9007199254740992), (467346614753249/9007199254740992)), (5403971/562949953421312), by norm_num⟩
  | 1 => ⟨((-949699587/4294967296), (-603484199/4294967296)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((1285917079/4294967296), (817132753/4294967296)), (157/4294967296), by norm_num⟩
  | 3 => ⟨((-1160776001/4294967296), (-184403043/1073741824)), (9/268435456), by norm_num⟩
  | 4 => ⟨((785859921/4294967296), (249686349/2147483648)), (25/1073741824), by norm_num⟩
  | 5 => ⟨((-851259247/8589934592), (-270465267/4294967296)), (55/4294967296), by norm_num⟩
  | 6 => ⟨((96052199/2147483648), (244144507/8589934592)), (101/17179869184), by norm_num⟩
  | 7 => ⟨((-297273345/17179869184), (-377803189/34359738368)), (159/68719476736), by norm_num⟩
  | 8 => ⟨((402515571/68719476736), (511555001/137438953472)), (55/68719476736), by norm_num⟩
  | 9 => ⟨((-968917665/549755813888), (-615696277/549755813888)), (67/274877906944), by norm_num⟩
  | 10 => ⟨((1049551071/2199023255552), (666934571/2199023255552)), (147/2199023255552), by norm_num⟩
  | 11 => ⟨((-1033540723/8796093022208), (-164190209/2199023255552)), (147/8796093022208), by norm_num⟩
  | 12 => ⟨((466480027/17592186044416), (592847105/35184372088832)), (135/35184372088832), by norm_num⟩
  | 13 => ⟨((-388692717/70368744177664), (-493987607/140737488355328)), (57/70368744177664), by norm_num⟩
  | 14 => ⟨((300742683/281474976710656), (191106177/281474976710656)), (179/1125899906842624), by norm_num⟩
  | 15 => ⟨((-868721369/4503599627370496), (-138006699/1125899906842624)), (131/4503599627370496), by norm_num⟩
  | 16 => ⟨((1176270539/36028797018963968), (373729069/18014398509481984)), (45/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (737378301033/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889183149929833/316912650057057350374175801344), (872272885685/633825300114114700748351602688)), (46143/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889289186437871/39614081257132168796771975168), (490554019891/19807040628566084398385987584)), (25957/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889036116660495/2475880078570760549798248448), (521089504647/1237940039285380274899124224)), (27581/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770702533007135/154742504910672534362390528), (520949905039/77371252455336267181195264)), (110331/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549095957833645/9671406556917033397649408), (976484526621/9671406556917033397649408)), (103443/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258388576631777/604462909807314587353088), (854127532323/604462909807314587353088)), (11315/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943571101509237/37778931862957161709568), (693700842425/37778931862957161709568)), (147109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81065772607073/295147905179352825856), (1040065400937/4722366482869645213696)), (13793/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620778833912747/590295810358705651712), (1429300864277/590295810358705651712)), (2371/9223372036854775808), by norm_num⟩
  | 8 => ⟨((911319360745057/36893488147419103232), (1785443300319/73786976294838206464)), (189711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910858731457073/4611686018427387904), (125437419401/576460752303423488)), (53367/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592967153861633/1152921504606846976), (125310589733/72057594037927936)), (13345/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193690725486013/144115188075855872), (876034019803/72057594037927936)), (93445/72057594037927936), by norm_num⟩
  | 4 => ⟨((186288125472465/4503599627370496), (2623548410873/36028797018963968)), (280455/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487596826798115/9007199254740992), (3271481870669/9007199254740992)), (87695/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224640267972225/4503599627370496), (6519163662135/4503599627370496)), (702193/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105588314202241/1125899906842624), (9719457736469/2251799813685248)), (263721/562949953421312), by norm_num⟩
  | 0 => ⟨((1085508247501995/1125899906842624), (19203034846155/2251799813685248)), (264525/281474976710656), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085508247501995/1125899906842624), (19203034846155/2251799813685248)), (1009082795263194949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2092967517089809/2251799813685248), (9257062983967/562949953421312)), (4116657/2251799813685248), by norm_num⟩
  | 2 => ⟨((1944729682246861/2251799813685248), (17208218964535/562949953421312)), (973495/281474976710656), by norm_num⟩
  | 3 => ⟨((838714780340827/1125899906842624), (118892750574185/2251799813685248)), (13928011/2251799813685248), by norm_num⟩
  | 4 => ⟨((1243287448508901/2251799813685248), (177133165347855/2251799813685248)), (2777689/281474976710656), by norm_num⟩
  | 5 => ⟨((672523157764725/2251799813685248), (195601260692193/2251799813685248)), (14017185/1125899906842624), by norm_num⟩
  | 6 => ⟨((735460660453423/9007199254740992), (467346614753249/9007199254740992)), (5403971/562949953421312), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-234808005/4194304)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile015Terms1

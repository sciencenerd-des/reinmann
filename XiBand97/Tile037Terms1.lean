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
namespace Reinmann.XiBand97.Tile037Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33621/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33621/1280))
  have he : value ((69/80), (33621/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1936533423/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((267502315564473/4503599627370496), (-1243605138778617/9007199254740992)), (93420557/4503599627370496), by norm_num⟩
  | 1 => ⟨((-560534155/4294967296), (1302947891/4294967296)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((615809711/4294967296), (-1431434565/4294967296)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((-451024077/4294967296), (1048394403/4294967296)), (41/1073741824), by norm_num⟩
  | 4 => ⟨((247750297/4294967296), (-1151778975/8589934592)), (183/8589934592), by norm_num⟩
  | 5 => ⟨((-435490433/17179869184), (1012286829/17179869184)), (163/17179869184), by norm_num⟩
  | 6 => ⟨((318956761/34359738368), (-741407167/34359738368)), (241/68719476736), by norm_num⟩
  | 7 => ⟨((-400468363/137438953472), (930878885/137438953472)), (77/68719476736), by norm_num⟩
  | 8 => ⟨((439959465/549755813888), (-1022674983/549755813888)), (171/549755813888), by norm_num⟩
  | 9 => ⟨((-429639889/2199023255552), (998687381/2199023255552)), (169/2199023255552), by norm_num⟩
  | 10 => ⟨((188803065/4398046511104), (-109717023/1099511627776)), (151/8796093022208), by norm_num⟩
  | 11 => ⟨((-301703807/35184372088832), (701303097/35184372088832)), (61/17592186044416), by norm_num⟩
  | 12 => ⟨((55242585/35184372088832), (-256820067/70368744177664)), (181/281474976710656), by norm_num⟩
  | 13 => ⟨((-149391219/562949953421312), (694512447/1125899906842624)), (31/281474976710656), by norm_num⟩
  | 14 => ⟨((23446147/562949953421312), (-108999987/1125899906842624)), (157/9007199254740992), by norm_num⟩
  | 15 => ⟨((-109901761/18014398509481984), (255463947/18014398509481984)), (93/36028797018963968), by norm_num⟩
  | 16 => ⟨((482957701/576460752303423488), (-561311663/288230376151711744)), (207/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1516924642847/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779044133937393/633825300114114700748351602688), (-1795733299923/633825300114114700748351602688)), (92377/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945025766698071/19807040628566084398385987584), (-2019862667627/39614081257132168796771975168)), (203/77371252455336267181195264), by norm_num⟩
  | 15 => ⟨((59057682445761/77371252455336267181195264), (-2145689046501/2475880078570760549798248448)), (27611/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771511948716027/154742504910672534362390528), (-536305564457/38685626227668133590597632)), (110459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387463615044421/2417851639229258349412352), (-2010650029569/9671406556917033397649408)), (103571/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259051941446441/604462909807314587353088), (-879411540133/302231454903657293676544)), (90641/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236027445284145/9444732965739290427392), (-714289594213/18889465931478580854784)), (18415/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324464962241893/1180591620717411303424), (-2142056095721/4722366482869645213696)), (110517/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621888264667829/590295810358705651712), (-23000055303/4611686018427387904)), (76001/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824024214624861/73786976294838206464), (-1839014877399/36893488147419103232)), (190065/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823274363297727/9223372036854775808), (-2067531910569/4611686018427387904)), (213909/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99657614530453/72057594037927936), (-2065833327391/576460752303423488)), (107009/576460752303423488), by norm_num⟩
  | 5 => ⟨((597524286608323/72057594037927936), (-3611389808541/144115188075855872)), (46847/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492336791758643/36028797018963968), (-2704727961041/18014398509481984)), (281325/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490127859574517/9007199254740992), (-6748488037043/9007199254740992)), (88021/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229676303315379/4503599627370496), (-13457054463271/4503599627370496)), (352727/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218665872567213/2251799813685248), (-10043018113565/1125899906842624)), (265351/562949953421312), by norm_num⟩
  | 0 => ⟨((1092868671321643/1125899906842624), (-19887719405771/1125899906842624)), (2135743/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092868671321643/1125899906842624), (-19887719405771/1125899906842624)), (8147212990767668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120910400856905/2251799813685248), (-77217043364195/2251799813685248)), (4221623/2251799813685248), by norm_num⟩
  | 2 => ⟨((62343164751137/70368744177664), (-18182170257679/281474976710656)), (515125/140737488355328), by norm_num⟩
  | 3 => ⟨((1758057002908781/2251799813685248), (-257735799984335/2251799813685248)), (3917199/562949953421312), by norm_num⟩
  | 4 => ⟨((1343075287822089/2251799813685248), (-201223139512211/1125899906842624)), (14026579/1125899906842624), by norm_num⟩
  | 5 => ⟨((364572421420247/1125899906842624), (-240037168823217/1125899906842624)), (21745891/1125899906842624), by norm_num⟩
  | 6 => ⟨((267502315564473/4503599627370496), (-1243605138778617/9007199254740992)), (93420557/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1936533423/33554432)), (1/16777216), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-2029393371/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-434883105427871/4503599627370496), (439233543327217/4503599627370496)), (84211123/2251799813685248), by norm_num⟩
  | 1 => ⟨((954966885/4294967296), (-482260041/2147483648)), (373/4294967296), by norm_num⟩
  | 2 => ⟨((-549723129/2147483648), (555222391/2147483648)), (217/2147483648), by norm_num⟩
  | 3 => ⟨((210964047/1073741824), (-852297867/4294967296)), (335/4294967296), by norm_num⟩
  | 4 => ⟨((-242881335/2147483648), (490622091/4294967296)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((447403953/8589934592), (-903759291/17179869184)), (45/2147483648), by norm_num⟩
  | 6 => ⟨((-686790449/34359738368), (346830445/17179869184)), (279/34359738368), by norm_num⟩
  | 7 => ⟨((112956675/17179869184), (-912693271/137438953472)), (185/68719476736), by norm_num⟩
  | 8 => ⟨((-65023089/34359738368), (8209195/4294967296)), (429/549755813888), by norm_num⟩
  | 9 => ⟨((1064684057/2199023255552), (-1075334829/2199023255552)), (221/1099511627776), by norm_num⟩
  | 10 => ⟨((-980610255/8796093022208), (990419979/8796093022208)), (205/4398046511104), by norm_num⟩
  | 11 => ⟨((410534283/17592186044416), (-207320571/8796093022208)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((-315096707/70368744177664), (636497675/140737488355328)), (67/35184372088832), by norm_num⟩
  | 13 => ⟨((892968591/1125899906842624), (-450950787/562949953421312)), (191/562949953421312), by norm_num⟩
  | 14 => ⟨((-146866869/1125899906842624), (9271005/70368744177664)), (253/4503599627370496), by norm_num⟩
  | 15 => ⟨((360718361/18014398509481984), (-728653753/36028797018963968)), (313/36028797018963968), by norm_num⟩
  | 16 => ⟨((-830584721/288230376151711744), (838893635/288230376151711744)), (181/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (1531361704947/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889449353805031/316912650057057350374175801344), (3625104154025/633825300114114700748351602688)), (138835/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944943827588857/19807040628566084398385987584), (509689761645/4951760157141521099596496896)), (2441/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((472417840182501/618970019642690137449562112), (2165741800285/1237940039285380274899124224)), (41507/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771337069953289/154742504910672534362390528), (4330494415379/154742504910672534362390528)), (20759/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774845042654657/4835703278458516698824704), (4058787677069/9671406556917033397649408)), (38935/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629453843859857/302231454903657293676544), (3550388573251/604462909807314587353088)), (136321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887984352409461/75557863725914323419136), (1441852971071/18889465931478580854784)), (110805/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297682744367845/4722366482869645213696), (4323835970103/4722366482869645213696)), (83143/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621643614128877/590295810358705651712), (185702357711/18446744073709551616)), (114385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911858353023123/36893488147419103232), (3711948569515/36893488147419103232)), (286153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822926088483033/9223372036854775808), (8346115366351/9223372036854775808)), (40273/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594170653365261/1152921504606846976), (2084726878433/288230376151711744)), (20157/72057594037927936), by norm_num⟩
  | 5 => ⟨((597369015690609/72057594037927936), (7288439768775/144115188075855872)), (35321/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491864476880575/36028797018963968), (5458231185971/18014398509481984)), (424591/36028797018963968), by norm_num⟩
  | 3 => ⟨((744763063940875/4503599627370496), (13617258240853/9007199254740992)), (532035/9007199254740992), by norm_num⟩
  | 2 => ⟨((278554873478471/562949953421312), (6787414876493/1125899906842624)), (266991/1125899906842624), by norm_num⟩
  | 1 => ⟨((554181458831799/562949953421312), (20256352531459/1125899906842624)), (402925/562949953421312), by norm_num⟩
  | 0 => ⟨((1090762199225629/1125899906842624), (40090213605563/1125899906842624)), (1631275/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090762199225629/1125899906842624), (40090213605563/1125899906842624)), (6222820286277389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263823396469707/281474976710656), (77678112048981/1125899906842624)), (1638451/562949953421312), by norm_num⟩
  | 2 => ⟨((122969486072211/140737488355328), (72806839142873/562949953421312)), (3297485/562949953421312), by norm_num⟩
  | 3 => ⟨((1681450187986705/2251799813685248), (63615030341717/281474976710656)), (26461175/2251799813685248), by norm_num⟩
  | 4 => ⟨((1140543180440705/2251799813685248), (380017811802915/1125899906842624)), (51478623/2251799813685248), by norm_num⟩
  | 5 => ⟨((642316952781293/4503599627370496), (1539841050038909/4503599627370496)), (173797299/4503599627370496), by norm_num⟩
  | 6 => ⟨((-434883105427871/4503599627370496), (439233543327217/4503599627370496)), (84211123/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-2029393371/33554432)), (3/33554432), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-528348853/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1125476166666715/9007199254740992), (-86338345661611/4503599627370496)), (10129461/562949953421312), by norm_num⟩
  | 1 => ⟨((-1286875715/4294967296), (98719745/2147483648)), (187/4294967296), by norm_num⟩
  | 2 => ⟨((1542896597/4294967296), (-118359805/2147483648)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((-1233234819/4294967296), (189209611/4294967296)), (183/4294967296), by norm_num⟩
  | 4 => ⟨((1478583971/8589934592), (-3544569/134217728)), (111/4294967296), by norm_num⟩
  | 5 => ⟨((-709097903/8589934592), (108793667/8589934592)), (215/17179869184), by norm_num⟩
  | 6 => ⟨((1133561673/34359738368), (-173917213/34359738368)), (87/17179869184), by norm_num⟩
  | 7 => ⟨((-776617765/68719476736), (238305865/137438953472)), (241/137438953472), by norm_num⟩
  | 8 => ⟨((465562017/137438953472), (-142858127/274877906944)), (73/137438953472), by norm_num⟩
  | 9 => ⟨((-248081991/274877906944), (9515523/68719476736)), (157/1099511627776), by norm_num⟩
  | 10 => ⟨((475899707/2199023255552), (-146030257/4398046511104)), (153/4398046511104), by norm_num⟩
  | 11 => ⟨((-414966421/8796093022208), (127332823/17592186044416)), (269/35184372088832), by norm_num⟩
  | 12 => ⟨((663364013/70368744177664), (-101776925/70368744177664)), (217/140737488355328), by norm_num⟩
  | 13 => ⟨((-978878419/562949953421312), (75092433/281474976710656)), (81/281474976710656), by norm_num⟩
  | 14 => ⟨((1341284533/4503599627370496), (-205787189/4503599627370496)), (7/140737488355328), by norm_num⟩
  | 15 => ⟨((-857669291/18014398509481984), (263176601/36028797018963968)), (289/36028797018963968), by norm_num⟩
  | 16 => ⟨((1028300569/144115188075855872), (-78883741/72057594037927936)), (175/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-198307421417/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111173685967131/39614081257132168796771975168), (-234689015335/633825300114114700748351602688)), (92223/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472438344676073/9903520314283042199192993792), (-131988749611/19807040628566084398385987584)), (207505/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889529238060959/2475880078570760549798248448), (-140208468239/1237940039285380274899124224)), (110239/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221399445147997/19342813113834066795298816), (-280350410511/154742504910672534362390528)), (110241/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549558072719971/9671406556917033397649408), (-65689462081/2417851639229258349412352)), (103353/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78674551759441/37778931862957161709568), (-28730310107/75557863725914323419136)), (22609/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943899463074941/37778931862957161709568), (-373361641409/75557863725914323419136)), (293925/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648772370861015/2361183241434822606848), (-17494090195/295147905179352825856)), (110225/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621455592715351/590295810358705651712), (-384681928769/590295810358705651712)), (151565/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911742137295349/36893488147419103232), (-480570502357/73786976294838206464)), (378929/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822668166736331/9223372036854775808), (-270127237235/4611686018427387904)), (426319/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796958589403895/576460752303423488), (-269885361871/576460752303423488)), (426349/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194521234119851/144115188075855872), (-471755747681/144115188075855872)), (373089/144115188075855872), by norm_num⟩
  | 4 => ⟨((745774620847767/18014398509481984), (-706547808569/36028797018963968)), (559699/36028797018963968), by norm_num⟩
  | 3 => ⟨((744574729212407/4503599627370496), (-440643932191/4503599627370496)), (699741/9007199254740992), by norm_num⟩
  | 2 => ⟨((139233596630385/281474976710656), (-439224530431/1125899906842624)), (699919/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107901312634545/1125899906842624), (-1310599423343/1125899906842624)), (2100663/2251799813685248), by norm_num⟩
  | 0 => ⟨((1090094531243797/1125899906842624), (-40516231257/17592186044416)), (2102509/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1090094531243797/1125899906842624), (-40516231257/17592186044416)), (8020435337546920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2110843701070687/2251799813685248), (-5021152232969/1125899906842624)), (4080977/1125899906842624), by norm_num⟩
  | 2 => ⟨((1978666245281783/2251799813685248), (-9413685442787/1125899906842624)), (15374879/2251799813685248), by norm_num⟩
  | 3 => ⟨((434626294989809/562949953421312), (-33087384617657/2251799813685248)), (13638523/1125899906842624), by norm_num⟩
  | 4 => ⟨((670864582935473/1125899906842624), (-51090322682779/2251799813685248)), (5365021/281474976710656), by norm_num⟩
  | 5 => ⟨((399153362246477/1125899906842624), (-121768152960375/4503599627370496)), (106190697/4503599627370496), by norm_num⟩
  | 6 => ⟨((1125476166666715/9007199254740992), (-86338345661611/4503599627370496)), (10129461/562949953421312), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-528348853/8388608)), (1/8388608), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1095041633/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-402636875168633/4503599627370496), (-683628846138653/9007199254740992)), (192323901/4503599627370496), by norm_num⟩
  | 1 => ⟨((954165505/4294967296), (405014483/2147483648)), (229/2147483648), by norm_num⟩
  | 2 => ⟨((-148188263/536870912), (-503211591/2147483648)), (143/1073741824), by norm_num⟩
  | 3 => ⟨((490978667/2147483648), (104202819/536870912)), (119/1073741824), by norm_num⟩
  | 4 => ⟨((-610018077/4294967296), (-129467139/1073741824)), (149/2147483648), by norm_num⟩
  | 5 => ⟨((303167595/4294967296), (514742007/8589934592)), (149/4294967296), by norm_num⟩
  | 6 => ⟨((-251114391/8589934592), (-852723891/34359738368)), (31/2147483648), by norm_num⟩
  | 7 => ⟨((22285565/2147483648), (605411219/68719476736)), (177/34359738368), by norm_num⟩
  | 8 => ⟨((-443020389/137438953472), (-376097591/137438953472)), (221/137438953472), by norm_num⟩
  | 9 => ⟨((489273027/549755813888), (415363291/549755813888)), (245/549755813888), by norm_num⟩
  | 10 => ⟨((-486319119/2199023255552), (-825711203/4398046511104)), (489/4398046511104), by norm_num⟩
  | 11 => ⟨((109859783/2199023255552), (46632165/1099511627776)), (111/4398046511104), by norm_num⟩
  | 12 => ⟨((-363988407/35184372088832), (-309004205/35184372088832)), (369/70368744177664), by norm_num⟩
  | 13 => ⟨((1113202723/562949953421312), (472520987/281474976710656)), (567/562949953421312), by norm_num⟩
  | 14 => ⟨((-395172121/1125899906842624), (-167738649/562949953421312)), (405/2251799813685248), by norm_num⟩
  | 15 => ⟨((261857555/4503599627370496), (444602543/9007199254740992)), (539/18014398509481984), by norm_num⟩
  | 16 => ⟨((-162672895/18014398509481984), (-138099477/18014398509481984)), (337/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-793848819773/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778655760682601/633825300114114700748351602688), (-1878744844679/316912650057057350374175801344)), (185139/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944807181312559/19807040628566084398385987584), (-4226368873133/39614081257132168796771975168)), (208329/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889381010067895/2475880078570760549798248448), (-2244766699011/1237940039285380274899124224)), (221405/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885523372429031/77371252455336267181195264), (-4488427080117/154742504910672534362390528)), (221467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387354483183553/2417851639229258349412352), (-4206725146149/9671406556917033397649408)), (207691/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258669581459671/604462909807314587353088), (-3679709510081/604462909807314587353088)), (45449/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887597480905929/75557863725914323419136), (-5977325370899/75557863725914323419136)), (295541/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20271759931267/73786976294838206464), (-560133412089/590295810358705651712)), (55441/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202655598454785/73786976294838206464), (-3079168792919/295147905179352825856)), (305101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911609141408195/36893488147419103232), (-3846614398615/36893488147419103232)), (47705/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822365513906015/9223372036854775808), (-8648432088853/9223372036854775808)), (107427/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593610268932837/1152921504606846976), (-8640373437743/1152921504606846976)), (215081/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194247909874071/144115188075855872), (-3775633300023/72057594037927936)), (376903/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491129726751485/36028797018963968), (-11308794153973/36028797018963968)), (566377/36028797018963968), by norm_num⟩
  | 3 => ⟨((744304225903299/4503599627370496), (-1763042555301/1125899906842624)), (177441/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113302970880357/2251799813685248), (-7028463868345/1125899906842624)), (712457/2251799813685248), by norm_num⟩
  | 1 => ⟨((553495526406757/562949953421312), (-20967089943019/1125899906842624)), (1075435/1125899906842624), by norm_num⟩
  | 0 => ⟨((544015184566065/562949953421312), (-41462355905811/1125899906842624)), (2177963/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544015184566065/562949953421312), (-41462355905811/1125899906842624)), (8308269505027389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524953839152315/562949953421312), (-80135546911619/1125899906842624)), (4369827/1125899906842624), by norm_num⟩
  | 2 => ⟨((1946681797243233/2251799813685248), (-298907302492245/2251799813685248)), (17543633/2251799813685248), by norm_num⟩
  | 3 => ⟨((1643229749708187/2251799813685248), (-516810953876439/2251799813685248)), (34990493/2251799813685248), by norm_num⟩
  | 4 => ⟨((1080518096454311/2251799813685248), (-754275872325421/2251799813685248)), (16782329/562949953421312), by norm_num⟩
  | 5 => ⟨((265826145625857/2251799813685248), (-1447746331291595/4503599627370496)), (218791149/4503599627370496), by norm_num⟩
  | 6 => ⟨((-402636875168633/4503599627370496), (-683628846138653/9007199254740992)), (192323901/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1095041633/16777216)), (1/8388608), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1130314627/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-168965771559879/9007199254740992), (485634443974099/4503599627370496)), (166384435/4503599627370496), by norm_num⟩
  | 1 => ⟨((206655811/4294967296), (-593961599/2147483648)), (409/4294967296), by norm_num⟩
  | 2 => ⟨((-265030845/4294967296), (761740711/2147483648)), (527/4294967296), by norm_num⟩
  | 3 => ⟨((226596899/4294967296), (-651275449/2147483648)), (453/4294967296), by norm_num⟩
  | 4 => ⟨((-290604785/8589934592), (1670488545/8589934592)), (583/8589934592), by norm_num⟩
  | 5 => ⟨((298154623/17179869184), (-107117963/1073741824)), (601/17179869184), by norm_num⟩
  | 6 => ⟨((-127458585/17179869184), (732672401/17179869184)), (129/8589934592), by norm_num⟩
  | 7 => ⟨((46703545/17179869184), (-1073867203/68719476736)), (95/17179869184), by norm_num⟩
  | 8 => ⟨((-29948057/34359738368), (172150937/34359738368)), (245/137438953472), by norm_num⟩
  | 9 => ⟨((273120887/1099511627776), (-392496387/274877906944)), (561/1099511627776), by norm_num⟩
  | 10 => ⟨((-280216497/4398046511104), (1610773369/4398046511104)), (289/2199023255552), by norm_num⟩
  | 11 => ⟨((261360409/17592186044416), (-1502382589/17592186044416)), (271/8796093022208), by norm_num⟩
  | 12 => ⟨((-111729369/35184372088832), (160563969/8796093022208)), (233/35184372088832), by norm_num⟩
  | 13 => ⟨((88178515/140737488355328), (-1013756183/281474976710656)), (185/140737488355328), by norm_num⟩
  | 14 => ⟨((-258483915/2251799813685248), (1485847583/2251799813685248)), (545/2251799813685248), by norm_num⟩
  | 15 => ⟨((176799507/9007199254740992), (-1016299681/9007199254740992)), (187/4503599627370496), by norm_num⟩
  | 16 => ⟨((-226740891/72057594037927936), (1303378607/72057594037927936)), (481/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (2270499720299/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222319130991277/79228162514264337593543950336), (2686407957389/633825300114114700748351602688)), (184929/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472374760488391/9903520314283042199192993792), (3021621011723/39614081257132168796771975168)), (208079/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889258781550317/2475880078570760549798248448), (1604873660897/1237940039285380274899124224)), (221123/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770924853255399/154742504910672534362390528), (3208931922735/154742504910672534362390528)), (13823/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549304017110979/9671406556917033397649408), (751876887299/2417851639229258349412352)), (6481/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258570262798647/604462909807314587353088), (657675809841/151115727451828646838272)), (181515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943718378945697/37778931862957161709568), (2136634910947/37778931862957161709568)), (295049/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648636339451769/2361183241434822606848), (100110401531/147573952589676412928)), (221365/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405270199436243/147573952589676412928), (4402551995409/590295810358705651712)), (152251/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455753679898485/18446744073709551616), (5499733312519/73786976294838206464)), (23801/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822138460711061/9223372036854775808), (6182450005657/9223372036854775808)), (428677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796692827938617/576460752303423488), (3088258494897/576460752303423488)), (214501/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194054112908495/144115188075855872), (674722979481/18014398509481984)), (187871/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490844495989125/36028797018963968), (8083353965591/36028797018963968)), (70543/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488261444581943/9007199254740992), (10080913664683/9007199254740992)), (706713/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112970196667769/2251799813685248), (20092128172523/4503599627370496)), (1417279/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213054502263575/2251799813685248), (7491106015153/562949953421312)), (2135577/2251799813685248), by norm_num⟩
  | 0 => ⟨((543621435533013/562949953421312), (59236648877263/2251799813685248)), (1077483/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543621435533013/562949953421312), (59236648877263/2251799813685248)), (4110271456004905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2098267898171967/2251799813685248), (57202797341245/1125899906842624)), (8550665/2251799813685248), by norm_num⟩
  | 2 => ⟨((974695775736023/1125899906842624), (213210415272817/2251799813685248)), (8402093/1125899906842624), by norm_num⟩
  | 3 => ⟨((833703936946547/1125899906842624), (369154113694027/2251799813685248)), (32277085/2251799813685248), by norm_num⟩
  | 4 => ⟨((573320526961/1099511627776), (546700885320781/2251799813685248)), (29191887/1125899906842624), by norm_num⟩
  | 5 => ⟨((959029192957037/4503599627370496), (570134652047555/2251799813685248)), (11154453/281474976710656), by norm_num⟩
  | 6 => ⟨((-168965771559879/9007199254740992), (485634443974099/4503599627370496)), (166384435/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1130314627/16777216)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-581486159/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((905728038721105/9007199254740992), (-46728898824115/2251799813685248)), (138232317/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1139768705/4294967296), (235214697/4294967296)), (11/268435456), by norm_num⟩
  | 2 => ⟨((1503957477/4294967296), (-310372535/4294967296)), (117/2147483648), by norm_num⟩
  | 3 => ⟨((-1323010001/4294967296), (8532197/134217728)), (13/268435456), by norm_num⟩
  | 4 => ⟨((436437405/2147483648), (-22516957/536870912)), (277/8589934592), by norm_num⟩
  | 5 => ⟨((-460713333/4294967296), (190155329/8589934592)), (37/2147483648), by norm_num⟩
  | 6 => ⟨((202641483/4294967296), (-83638469/8589934592)), (263/34359738368), by norm_num⟩
  | 7 => ⟨((-1222359979/68719476736), (126129551/34359738368)), (25/8589934592), by norm_num⟩
  | 8 => ⟨((1612939031/274877906944), (-83215779/68719476736)), (133/137438953472), by norm_num⟩
  | 9 => ⟨((-472959841/274877906944), (97604983/274877906944)), (79/274877906944), by norm_num⟩
  | 10 => ⟨((249633627/549755813888), (-206068117/2199023255552)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((-958250841/8796093022208), (98877377/4398046511104)), (41/2199023255552), by norm_num⟩
  | 12 => ⟨((842959635/35184372088832), (-347924089/70368744177664)), (291/70368744177664), by norm_num⟩
  | 13 => ⟨((-684498093/140737488355328), (141260249/140737488355328)), (239/281474976710656), by norm_num⟩
  | 14 => ⟨((258061387/281474976710656), (-213025083/1125899906842624)), (91/562949953421312), by norm_num⟩
  | 15 => ⟨((-726441381/4503599627370496), (299832217/9007199254740992)), (129/4503599627370496), by norm_num⟩
  | 16 => ⟨((958560225/36028797018963968), (-98909301/18014398509481984)), (43/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-265099080935/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889229176592327/316912650057057350374175801344), (-313626613559/633825300114114700748351602688)), (92231/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236174093191827/4951760157141521099596496896), (-176380100145/19807040628566084398385987584)), (51881/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889146148484209/2475880078570760549798248448), (-187360360501/1237940039285380274899124224)), (220499/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770812565132805/154742504910672534362390528), (-374622896701/154742504910672534362390528)), (27563/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387299778315203/2417851639229258349412352), (-43888132925/1208925819614629174706176)), (25841/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258478837926969/604462909807314587353088), (-307113068801/604462909807314587353088)), (180893/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471822219537875/18889465931478580854784), (-124716020591/18889465931478580854784)), (293961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297162368497813/4722366482869645213696), (-23373614081/295147905179352825856)), (220481/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620930093896951/590295810358705651712), (-513943036953/590295810358705651712)), (303175/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911413898681799/36893488147419103232), (-642014369289/73786976294838206464)), (378991/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821930174354397/9223372036854775808), (-721696786909/9223372036854775808)), (106599/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796589933218549/576460752303423488), (-2816350589/4503599627370496)), (426435/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596938424983773/72057594037927936), (-157515889995/36028797018963968)), (373175/144115188075855872), by norm_num⟩
  | 4 => ⟨((186323023964023/4503599627370496), (-58968734515/2251799813685248)), (559851/36028797018963968), by norm_num⟩
  | 3 => ⟨((371986453039677/2251799813685248), (-588293852431/4503599627370496)), (699971/9007199254740992), by norm_num⟩
  | 2 => ⟨((556334558341015/1125899906842624), (-1172417792121/2251799813685248)), (700207/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212223539963343/2251799813685248), (-437059698005/281474976710656)), (1050911/1125899906842624), by norm_num⟩
  | 0 => ⟨((543277508432097/562949953421312), (-3455146569291/1125899906842624)), (4208537/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543277508432097/562949953421312), (-3455146569291/1125899906842624)), (16054294594771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1048574442061797/1125899906842624), (-13337621989479/2251799813685248)), (254649/70368744177664), by norm_num⟩
  | 2 => ⟨((1953040196243317/2251799813685248), (-24843219989721/2251799813685248)), (7637387/1125899906842624), by norm_num⟩
  | 3 => ⟨((846822350589233/1125899906842624), (-43094245722167/2251799813685248)), (26833401/2251799813685248), by norm_num⟩
  | 4 => ⟨((636507571053609/1125899906842624), (-16206223234201/562949953421312)), (10347859/562949953421312), by norm_num⟩
  | 5 => ⟨((1435620764747007/4503599627370496), (-146590420325109/4503599627370496)), (12295747/562949953421312), by norm_num⟩
  | 6 => ⟨((905728038721105/9007199254740992), (-46728898824115/2251799813685248)), (138232317/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-581486159/8388608)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-596687951/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-375026182984513/9007199254740992), (-786556166762407/9007199254740992)), (155088297/9007199254740992), by norm_num⟩
  | 1 => ⟨((484270921/4294967296), (507839581/2147483648)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((-327857491/2147483648), (-1375255079/4294967296)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((295951515/2147483648), (1241419931/4294967296)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-100181445/1073741824), (-840456873/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((108518553/2147483648), (910399761/8589934592)), (189/8589934592), by norm_num⟩
  | 6 => ⟨((-195915793/8589934592), (-3210167/67108864)), (43/4294967296), by norm_num⟩
  | 7 => ⟨((606342631/68719476736), (1271704633/68719476736)), (269/68719476736), by norm_num⟩
  | 8 => ⟨((-410501571/137438953472), (-860959997/137438953472)), (23/17179869184), by norm_num⟩
  | 9 => ⟨((494070605/549755813888), (1036232397/549755813888)), (223/549755813888), by norm_num⟩
  | 10 => ⟨((-2090575/8589934592), (-280616935/549755813888)), (61/549755813888), by norm_num⟩
  | 11 => ⟨((263511601/4398046511104), (1105345087/8796093022208)), (243/8796093022208), by norm_num⟩
  | 12 => ⟨((-59466887/4398046511104), (-498888331/17592186044416)), (221/35184372088832), by norm_num⟩
  | 13 => ⟨((99101117/35184372088832), (207848407/35184372088832)), (93/70368744177664), by norm_num⟩
  | 14 => ⟨((-613418971/1125899906842624), (-160818263/140737488355328)), (145/562949953421312), by norm_num⟩
  | 15 => ⟨((221489249/2251799813685248), (929075049/4503599627370496)), (211/4503599627370496), by norm_num⟩
  | 16 => ⟨((-599804005/36028797018963968), (-157248867/4503599627370496)), (9/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-656421293021/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444590384729877/158456325028528675187087900672), (-776505756525/158456325028528675187087900672)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59040111418745/1237940039285380274899124224), (-873389520053/9903520314283042199192993792)), (104089/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889029794900143/2475880078570760549798248448), (-1855510139323/1237940039285380274899124224)), (110617/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770695818538939/154742504910672534362390528), (-1855012359873/77371252455336267181195264)), (110643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96818077879161/604462909807314587353088), (-3477090678613/9671406556917033397649408)), (103755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629191143609455/302231454903657293676544), (-3041397168289/604462909807314587353088)), (90813/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943565601140405/37778931862957161709568), (-617536109461/9444732965739290427392)), (73811/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297043428987407/4722366482869645213696), (-462935438185/590295810358705651712)), (110761/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810382722111113/295147905179352825856), (-5089474726079/590295810358705651712)), (152369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911310162963489/36893488147419103232), (-6357623000677/73786976294838206464)), (190571/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227711811416707/1152921504606846976), (-7146526445499/9223372036854775808)), (107271/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398235335563599/288230376151711744), (-7139282599787/1152921504606846976)), (214729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193664953109609/144115188075855872), (-3119365214209/72057594037927936)), (47025/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490259990266241/36028797018963968), (-2335457660315/9007199254740992)), (70643/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487529482508347/9007199254740992), (-5824433290525/4503599627370496)), (353957/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224472521786323/4503599627370496), (-5803159002135/1125899906842624)), (710143/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210842974085789/2251799813685248), (-34606798617897/2251799813685248)), (535401/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085012341732283/1125899906842624), (-4273031016419/140737488355328)), (541011/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085012341732283/1125899906842624), (-4273031016419/140737488355328)), (2063793184520530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((130571466848813/140737488355328), (-32942831676191/562949953421312)), (268895/140737488355328), by norm_num⟩
  | 2 => ⟨((1930525407956657/2251799813685248), (-30563241566837/281474976710656)), (4243311/1125899906842624), by norm_num⟩
  | 3 => ⟨((407134903537449/562949953421312), (-419242343200891/2251799813685248)), (512331/70368744177664), by norm_num⟩
  | 4 => ⟨((549866182036361/1125899906842624), (-606406270825875/2251799813685248)), (29818415/2251799813685248), by norm_num⟩
  | 5 => ⟨((747564416851561/4503599627370496), (-296156255876251/1125899906842624)), (90371001/4503599627370496), by norm_num⟩
  | 6 => ⟨((-375026182984513/9007199254740992), (-786556166762407/9007199254740992)), (155088297/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-596687951/8388608)), (1/16777216), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile037Terms1

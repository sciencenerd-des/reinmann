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
namespace Reinmann.XiBand97.Tile028Terms2
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
  | 0 => ⟨((-20060163/8388608), (-1117736289/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-656721591034395/9007199254740992), (249014999291233/4503599627370496)), (300803135/9007199254740992), by norm_num⟩
  | 1 => ⟨((868234099/4294967296), (-658432177/4294967296)), (25/268435456), by norm_num⟩
  | 2 => ⟨((-300907009/1073741824), (456390407/2147483648)), (557/4294967296), by norm_num⟩
  | 3 => ⟨((556194253/2147483648), (-843588597/4294967296)), (517/4294967296), by norm_num⟩
  | 4 => ⟨((-771048957/4294967296), (292365529/2147483648)), (361/4294967296), by norm_num⟩
  | 5 => ⟨((855120657/8589934592), (-648487495/8589934592)), (201/4294967296), by norm_num⟩
  | 6 => ⟨((-790299297/17179869184), (599329705/17179869184)), (373/17179869184), by norm_num⟩
  | 7 => ⟨((626049977/34359738368), (-474769937/34359738368)), (149/17179869184), by norm_num⟩
  | 8 => ⟨((-867889553/137438953472), (658170887/137438953472)), (415/137438953472), by norm_num⟩
  | 9 => ⟨((133683377/68719476736), (-405519373/274877906944)), (257/274877906944), by norm_num⟩
  | 10 => ⟨((-1186076875/2199023255552), (28108461/68719476736)), (143/549755813888), by norm_num⟩
  | 11 => ⟨((597909703/4398046511104), (-453429539/4398046511104)), (579/8796093022208), by norm_num⟩
  | 12 => ⟨((-138146475/4398046511104), (838115751/35184372088832)), (537/35184372088832), by norm_num⟩
  | 13 => ⟨((942826729/140737488355328), (-357500043/70368744177664)), (115/35184372088832), by norm_num⟩
  | 14 => ⟨((-746877359/562949953421312), (35400021/35184372088832)), (183/281474976710656), by norm_num⟩
  | 15 => ⟨((276104499/1125899906842624), (-418772049/2251799813685248)), (543/4503599627370496), by norm_num⟩
  | 16 => ⟨((-191381055/4503599627370496), (290270665/9007199254740992)), (189/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (811775831269/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444568258245795/158456325028528675187087900672), (3840769210643/633825300114114700748351602688)), (46289/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889183864994695/39614081257132168796771975168), (134998480353/1237940039285380274899124224)), (104175/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888923687290629/2475880078570760549798248448), (4588826981111/2475880078570760549798248448)), (221427/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221323689152417/19342813113834066795298816), (2293782856095/77371252455336267181195264)), (221491/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387247343733939/2417851639229258349412352), (4299503072005/9671406556917033397649408)), (51929/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258294690280649/604462909807314587353088), (1880362879425/302231454903657293676544)), (90909/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886988464484829/75557863725914323419136), (3054334340403/37778931862957161709568)), (73895/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324234008094799/1180591620717411303424), (2289652710167/2361183241434822606848)), (55449/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810308608430759/295147905179352825856), (6292977717103/590295810358705651712)), (305149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911217103772369/36893488147419103232), (3930436880881/36893488147419103232)), (190853/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821483963354509/9223372036854775808), (276129155185/288230376151711744)), (429791/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398182346643265/288230376151711744), (8826951465689/1152921504606846976)), (430255/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193477890250557/144115188075855872), (7713261623085/144115188075855872)), (94249/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489976204001887/36028797018963968), (11549271314935/36028797018963968)), (283271/18014398509481984), by norm_num⟩
  | 3 => ⟨((185896148637073/1125899906842624), (14400548765753/9007199254740992)), (177503/2251799813685248), by norm_num⟩
  | 2 => ⟨((277966919310087/562949953421312), (3586645345741/562949953421312)), (356385/1125899906842624), by norm_num⟩
  | 1 => ⟨((276212015655575/281474976710656), (2673159981709/140737488355328)), (1076067/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083784352721203/1125899906842624), (42234148951069/1125899906842624)), (1089947/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083784352721203/1125899906842624), (42234148951069/1125899906842624)), (4157817842723655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2083319827522871/2251799813685248), (162617332164193/2251799813685248)), (8720495/2251799813685248), by norm_num⟩
  | 2 => ⟨((239462733366265/281474976710656), (300900559932181/2251799813685248)), (8697791/1125899906842624), by norm_num⟩
  | 3 => ⟨((1589560703504155/2251799813685248), (511977806303319/2251799813685248)), (4280919/281474976710656), by norm_num⟩
  | 4 => ⟨((502838205735371/1125899906842624), (722817185630847/2251799813685248)), (31962047/1125899906842624), by norm_num⟩
  | 5 => ⟨((434248513366039/4503599627370496), (1291269657234671/4503599627370496)), (24534239/562949953421312), by norm_num⟩
  | 6 => ⟨((-656721591034395/9007199254740992), (249014999291233/4503599627370496)), (300803135/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1117736289/16777216)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1142176387/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((398655733336355/9007199254740992), (336503336015971/4503599627370496)), (205061907/9007199254740992), by norm_num⟩
  | 1 => ⟨((-538576481/4294967296), (-113652437/536870912)), (279/4294967296), by norm_num⟩
  | 2 => ⟨((190737759/1073741824), (322001601/1073741824)), (199/2147483648), by norm_num⟩
  | 3 => ⟨((-45033397/268435456), (-1216398977/4294967296)), (189/2147483648), by norm_num⟩
  | 4 => ⟨((510356885/4294967296), (861579453/4294967296)), (135/2147483648), by norm_num⟩
  | 5 => ⟨((-578379975/8589934592), (-976415361/8589934592)), (77/2147483648), by norm_num⟩
  | 6 => ⟨((546224621/17179869184), (461065505/8589934592)), (293/17179869184), by norm_num⟩
  | 7 => ⟨((-221081555/17179869184), (-746455395/34359738368)), (239/34359738368), by norm_num⟩
  | 8 => ⟨((156592803/34359738368), (1057433693/137438953472)), (85/34359738368), by norm_num⟩
  | 9 => ⟨((-788730345/549755813888), (-665763389/274877906944)), (215/274877906944), by norm_num⟩
  | 10 => ⟨((111732067/274877906944), (754499887/1099511627776)), (245/1099511627776), by norm_num⟩
  | 11 => ⟨((-28778253/274877906944), (-777330599/4398046511104)), (127/2199023255552), by norm_num⟩
  | 12 => ⟨((217426481/8796093022208), (734114475/17592186044416)), (121/8796093022208), by norm_num⟩
  | 13 => ⟨((-758173055/140737488355328), (-1279940263/140737488355328)), (53/17592186044416), by norm_num⟩
  | 14 => ⟨((153433287/140737488355328), (518049119/281474976710656)), (345/562949953421312), by norm_num⟩
  | 15 => ⟨((-115922463/562949953421312), (-195699157/562949953421312)), (131/1125899906842624), by norm_num⟩
  | 16 => ⟨((328433069/9007199254740992), (554457463/9007199254740992)), (373/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1349532453001/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222274876362725/79228162514264337593543950336), (798064405451/316912650057057350374175801344)), (92357/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889100972209169/39614081257132168796771975168), (1795264025663/39614081257132168796771975168)), (12989/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472209029307975/618970019642690137449562112), (1906992635137/2475880078570760549798248448)), (55209/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770502509102249/154742504910672534362390528), (1906458044877/154742504910672534362390528)), (220863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548908409459565/9671406556917033397649408), (446684153619/2417851639229258349412352)), (207087/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629112222944713/302231454903657293676544), (390706739905/151115727451828646838272)), (90615/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886875442073855/75557863725914323419136), (2538530077501/75557863725914323419136)), (147275/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296852248679723/4722366482869645213696), (1902967269455/4722366482869645213696)), (220959/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405125902476309/147573952589676412928), (653767292443/147573952589676412928)), (75973/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822294588935771/73786976294838206464), (3266571786015/73786976294838206464)), (189989/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910665086667257/4611686018427387904), (3671781866519/9223372036854775808)), (213815/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796289844762807/576460752303423488), (458487053485/144115188075855872)), (26739/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193351498707555/144115188075855872), (3205043478805/144115188075855872)), (93641/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489795775427741/36028797018963968), (4798846468413/36028797018963968)), (281141/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486959618282719/9007199254740992), (5983329573065/9007199254740992)), (703619/9007199254740992), by norm_num⟩
  | 2 => ⟨((555840964153143/1125899906842624), (2980272647669/1125899906842624)), (1409541/4503599627370496), by norm_num⟩
  | 1 => ⟨((552314278068887/562949953421312), (17768122959783/2251799813685248)), (2120091/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083579191765247/1125899906842624), (35084637211581/2251799813685248)), (1065857/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083579191765247/1125899906842624), (35084637211581/2251799813685248)), (4065921785594749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2085151841208271/2251799813685248), (33765863734471/1125899906842624)), (8339201/2251799813685248), by norm_num⟩
  | 2 => ⟨((60275363404351/70368744177664), (125067872389053/2251799813685248)), (15944279/2251799813685248), by norm_num⟩
  | 3 => ⟨((1645205006551759/2251799813685248), (107128691105049/1125899906842624)), (14542869/1125899906842624), by norm_num⟩
  | 4 => ⟨((1181629588731891/2251799813685248), (313080510763377/2251799813685248)), (48036097/2251799813685248), by norm_num⟩
  | 5 => ⟨((1153059051570119/4503599627370496), (657154677649351/4503599627370496)), (63771247/2251799813685248), by norm_num⟩
  | 6 => ⟨((398655733336355/9007199254740992), (336503336015971/4503599627370496)), (205061907/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1142176387/16777216)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1165219125/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((43912542060023/562949953421312), (-493017725409223/18014398509481984)), (124936785/9007199254740992), by norm_num⟩
  | 1 => ⟨((-484175001/2147483648), (169873775/2147483648)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((1399445749/4294967296), (-245499181/2147483648)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((-1348306157/4294967296), (473055933/4294967296)), (123/2147483648), by norm_num⟩
  | 4 => ⟨((974276509/4294967296), (-341826877/4294967296)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-1126408523/8589934592), (395202701/8589934592)), (105/4294967296), by norm_num⟩
  | 6 => ⟨((1085246461/17179869184), (-380760909/17179869184)), (51/4294967296), by norm_num⟩
  | 7 => ⟨((-448109389/17179869184), (314440165/34359738368)), (85/17179869184), by norm_num⟩
  | 8 => ⟨((1295202723/137438953472), (-227212243/68719476736)), (31/17179869184), by norm_num⟩
  | 9 => ⟨((-207978743/68719476736), (291879045/274877906944)), (161/274877906944), by norm_num⟩
  | 10 => ⟨((120227177/137438953472), (-337455579/1099511627776)), (47/274877906944), by norm_num⟩
  | 11 => ⟨((-1010912689/4398046511104), (354680755/4398046511104)), (25/549755813888), by norm_num⟩
  | 12 => ⟨((486985581/8796093022208), (-170859873/8796093022208)), (97/8796093022208), by norm_num⟩
  | 13 => ⟨((-866196535/70368744177664), (303906801/70368744177664)), (87/35184372088832), by norm_num⟩
  | 14 => ⟨((1430645715/562949953421312), (-250972467/281474976710656)), (145/281474976710656), by norm_num⟩
  | 15 => ⟨((-137836599/281474976710656), (193440995/1125899906842624)), (113/1125899906842624), by norm_num⟩
  | 16 => ⟨((398399013/4503599627370496), (-139779097/4503599627370496)), (165/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-439545006577/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889062141259181/316912650057057350374175801344), (-259909767751/316912650057057350374175801344)), (184503/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889016988573861/39614081257132168796771975168), (-584670985107/39614081257132168796771975168)), (207573/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944373498498563/1237940039285380274899124224), (-19407969617/77371252455336267181195264)), (220553/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770413515174441/154742504910672534362390528), (-77609685147/19342813113834066795298816)), (110281/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774412555881647/4835703278458516698824704), (-581884066793/9671406556917033397649408)), (103393/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258151694414785/604462909807314587353088), (-63620008377/75557863725914323419136)), (180947/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471689367995029/18889465931478580854784), (-826706858199/75557863725914323419136)), (36757/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648381995282567/2361183241434822606848), (-619721219913/4722366482869645213696)), (110279/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620382611209941/590295810358705651712), (-851614996033/590295810358705651712)), (303291/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227767984272505/9223372036854775808), (-531883391063/36893488147419103232)), (379151/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455290337952107/2305843009213693952), (-1195704588665/9223372036854775808)), (426595/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398102945500767/288230376151711744), (-597207323731/576460752303423488)), (106665/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193205605526233/144115188075855872), (-1043663500955/144115188075855872)), (46675/18014398509481984), by norm_num⟩
  | 4 => ⟨((372394745396571/9007199254740992), (-1562601284457/36028797018963968)), (560245/36028797018963968), by norm_num⟩
  | 3 => ⟨((371673048295063/2251799813685248), (-1948197639849/9007199254740992)), (350281/4503599627370496), by norm_num⟩
  | 2 => ⟨((555709913861421/1125899906842624), (-970318799769/1125899906842624)), (1401897/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208497249861677/2251799813685248), (-1446064638389/562949953421312)), (2104795/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165743322089517/2251799813685248), (-89209161431/17592186044416)), (2108753/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165743322089517/2251799813685248), (-89209161431/17592186044416)), (8044254307273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((260364715832029/281474976710656), (-1372798022021/140737488355328)), (2038857/562949953421312), by norm_num⟩
  | 2 => ⟨((1926487327428281/2251799813685248), (-20317439003649/1125899906842624)), (15246665/2251799813685248), by norm_num⟩
  | 3 => ⟨((823719365923535/1125899906842624), (-69528896003005/2251799813685248)), (26638295/2251799813685248), by norm_num⟩
  | 4 => ⟨((300783854246865/562949953421312), (-50868019244773/1125899906842624)), (40622697/2251799813685248), by norm_num⟩
  | 5 => ⟨((638238177900005/2251799813685248), (-217430040355943/4503599627370496)), (11770007/562949953421312), by norm_num⟩
  | 6 => ⟨((43912542060023/562949953421312), (-493017725409223/18014398509481984)), (124936785/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1165219125/16777216)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-296753921/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-93475132746449/18014398509481984), (-709126240294431/9007199254740992)), (234673833/18014398509481984), by norm_num⟩
  | 1 => ⟨((131240761/8589934592), (1991251891/8589934592)), (331/8589934592), by norm_num⟩
  | 2 => ⟨((-96607603/4294967296), (-1465779921/4294967296)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((94818397/4294967296), (719316589/2147483648)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-34898373/2147483648), (-1058991901/4294967296)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((10275613/1073741824), (1247254813/8589934592)), (107/4294967296), by norm_num⟩
  | 6 => ⟨((-80682441/17179869184), (-1224155229/17179869184)), (53/4294967296), by norm_num⟩
  | 7 => ⟨((33937789/17179869184), (257460741/8589934592)), (45/8589934592), by norm_num⟩
  | 8 => ⟨((-99927749/137438953472), (-1516154883/137438953472)), (267/137438953472), by norm_num⟩
  | 9 => ⟨((32692351/137438953472), (992050119/274877906944)), (351/549755813888), by norm_num⟩
  | 10 => ⟨((-38504253/549755813888), (-4564111/4294967296)), (13/68719476736), by norm_num⟩
  | 11 => ⟨((82453399/4398046511104), (1251025113/4398046511104)), (7/137438953472), by norm_num⟩
  | 12 => ⟨((-40463167/8796093022208), (-613927851/8796093022208)), (221/17592186044416), by norm_num⟩
  | 13 => ⟨((73317739/70368744177664), (278103553/17592186044416)), (101/35184372088832), by norm_num⟩
  | 14 => ⟨((-3854993/17592186044416), (-1871677581/562949953421312)), (171/281474976710656), by norm_num⟩
  | 15 => ⟨((96860089/2251799813685248), (367402695/562949953421312)), (135/1125899906842624), by norm_num⟩
  | 16 => ⟨((-71299655/9007199254740992), (-4225761/35184372088832)), (201/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-2131867004217/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778049184399137/633825300114114700748351602688), (-1260508881549/316912650057057350374175801344)), (92449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888932341139249/39614081257132168796771975168), (-2835517981121/39614081257132168796771975168)), (104021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236082105239093/309485009821345068724781056), (-3011957203687/2475880078570760549798248448)), (110541/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221290389504989/19342813113834066795298816), (-1505539653595/77371252455336267181195264)), (110561/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387185025870927/2417851639229258349412352), (-2821954398037/9671406556917033397649408)), (51837/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629038526659123/302231454903657293676544), (-617069499361/151115727451828646838272)), (90737/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943317847679279/37778931862957161709568), (-4009204803693/75557863725914323419136)), (4609/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((324168058592865/1180591620717411303424), (-1502687887503/2361183241434822606848)), (27663/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620255758836587/590295810358705651712), (-2064955184901/295147905179352825856)), (76103/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455496069740935/18446744073709551616), (-2579334214247/36893488147419103232)), (95173/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820980393980133/9223372036854775808), (-2899195798973/4611686018427387904)), (214261/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796114530850069/576460752303423488), (-2896004787945/576460752303423488)), (107207/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193043748019755/144115188075855872), (-316302299359/9007199254740992)), (23473/18014398509481984), by norm_num⟩
  | 4 => ⟨((372333063667959/9007199254740992), (-3788466225153/18014398509481984)), (70505/9007199254740992), by norm_num⟩
  | 3 => ⟨((371594229856747/2251799813685248), (-9446146721571/9007199254740992)), (44141/1125899906842624), by norm_num⟩
  | 2 => ⟨((2222188636363439/4503599627370496), (-18817420417807/4503599627370496)), (708069/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207469973702185/2251799813685248), (-28039589066065/2251799813685248)), (266663/562949953421312), by norm_num⟩
  | 0 => ⟨((2163488354176823/2251799813685248), (-55336847976197/2251799813685248)), (2151583/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163488354176823/2251799813685248), (-55336847976197/2251799813685248)), (8207637795455168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1014297086407/1099511627776), (-106333276542397/2251799813685248)), (4240153/2251799813685248), by norm_num⟩
  | 2 => ⟨((955632735491957/1125899906842624), (-196184432907217/2251799813685248)), (4111759/1125899906842624), by norm_num⟩
  | 3 => ⟨((401284269020445/562949953421312), (-10407245414349/70368744177664)), (1924089/281474976710656), by norm_num⟩
  | 4 => ⟨((136865786355807/281474976710656), (-237393116356851/1125899906842624)), (6624407/562949953421312), by norm_num⟩
  | 5 => ⟨((864589835824877/4503599627370496), (-923449634502617/4503599627370496)), (73885181/4503599627370496), by norm_num⟩
  | 6 => ⟨((-93475132746449/18014398509481984), (-709126240294431/9007199254740992)), (234673833/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-296753921/4194304)), (1/16777216), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-75480873/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-327414556922655/4503599627370496), (-365930984233645/18014398509481984)), (118884153/9007199254740992), by norm_num⟩
  | 1 => ⟨((935407977/4294967296), (261361899/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((-1401115933/4294967296), (-195742569/2147483648)), (259/4294967296), by norm_num⟩
  | 3 => ⟨((349780685/1073741824), (390928221/4294967296)), (65/1073741824), by norm_num⟩
  | 4 => ⟨((-1047849287/4294967296), (-4574673/67108864)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((1255630371/8589934592), (175417543/4294967296)), (237/8589934592), by norm_num⟩
  | 6 => ⟨((-626922071/8589934592), (-350335997/17179869184)), (239/17179869184), by norm_num⟩
  | 7 => ⟨((1073194675/34359738368), (299860815/34359738368)), (103/17179869184), by norm_num⟩
  | 8 => ⟨((-803750981/68719476736), (-449151361/137438953472)), (311/137438953472), by norm_num⟩
  | 9 => ⟨((535071723/137438953472), (299008273/274877906944)), (209/274877906944), by norm_num⟩
  | 10 => ⟨((-160293163/137438953472), (-358299493/1099511627776)), (253/1099511627776), by norm_num⟩
  | 11 => ⟨((698466039/2199023255552), (390316129/4398046511104)), (139/2199023255552), by norm_num⟩
  | 12 => ⟨((-1394944837/17592186044416), (-389760875/17592186044416)), (279/17592186044416), by norm_num⟩
  | 13 => ⟨((1285809621/70368744177664), (2806777/549755813888)), (259/70368744177664), by norm_num⟩
  | 14 => ⟨((-137569335/35184372088832), (-307505461/281474976710656)), (223/281474976710656), by norm_num⟩
  | 15 => ⟨((439595623/562949953421312), (245654409/1125899906842624)), (45/281474976710656), by norm_num⟩
  | 16 => ⟨((-1316910795/9007199254740992), (-367957421/9007199254740992)), (17/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1868682112259/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777973974884335/633825300114114700748351602688), (-4419259327095/633825300114114700748351602688)), (23159/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888847359765929/39614081257132168796771975168), (-2485264997559/19807040628566084398385987584)), (104243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944283026349439/1237940039285380274899124224), (-2639896807317/1237940039285380274899124224)), (110791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55319742776753/4835703278458516698824704), (-5278225071437/154742504910672534362390528)), (110827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548653873141183/9671406556917033397649408), (-4946669819423/9671406556917033397649408)), (103939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629000504978403/302231454903657293676544), (-4326670347287/604462909807314587353088)), (45493/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886511016408727/75557863725914323419136), (-3513858489463/37778931862957161709568)), (147925/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296577756391265/4722366482869645213696), (-1317014156707/1180591620717411303424)), (111007/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620124279537099/590295810358705651712), (-3619570784041/295147905179352825856)), (76369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821817575520271/73786976294838206464), (-9042275592679/73786976294838206464)), (95539/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820789621579787/9223372036854775808), (-2540854851819/2305843009213693952)), (26897/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592034259749533/1152921504606846976), (-10152001110583/1152921504606846976)), (53861/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192868775746637/144115188075855872), (-4435082850069/72057594037927936)), (94407/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489060786771599/36028797018963968), (-13279603801015/36028797018963968)), (283825/36028797018963968), by norm_num⟩
  | 3 => ⟨((743010944497337/4503599627370496), (-16554684514055/9007199254740992)), (355837/9007199254740992), by norm_num⟩
  | 2 => ⟨((555357943079403/1125899906842624), (-8243785199107/1125899906842624)), (178713/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103109329337829/1125899906842624), (-24563977557687/1125899906842624)), (540123/1125899906842624), by norm_num⟩
  | 0 => ⟨((135032972283603/140737488355328), (-48460889687155/1125899906842624)), (137031/140737488355328), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((135032972283603/140737488355328), (-48460889687155/1125899906842624)), (522731781542730287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((258597892612925/281474976710656), (-92993246510735/1125899906842624)), (1098999/562949953421312), by norm_num⟩
  | 2 => ⟨((235659975339459/281474976710656), (-42717576276115/281474976710656)), (8803589/2251799813685248), by norm_num⟩
  | 3 => ⟨((1526553678959565/2251799813685248), (-4470567459243/17592186044416)), (17413425/2251799813685248), by norm_num⟩
  | 4 => ⟨((889473360048041/2251799813685248), (-96982847735835/281474976710656)), (16230155/1125899906842624), by norm_num⟩
  | 5 => ⟨((5251349408603/140737488355328), (-612940165770373/2251799813685248)), (96025105/4503599627370496), by norm_num⟩
  | 6 => ⟨((-327414556922655/4503599627370496), (-365930984233645/18014398509481984)), (118884153/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-75480873/1048576)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1227363145/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-202633419352729/4503599627370496), (510609345896835/9007199254740992)), (476647375/18014398509481984), by norm_num⟩
  | 1 => ⟨((588342659/4294967296), (-741272741/4294967296)), (87/1073741824), by norm_num⟩
  | 2 => ⟨((-895611213/4294967296), (564205373/2147483648)), (133/1073741824), by norm_num⟩
  | 3 => ⟨((908902811/4294967296), (-1145157279/4294967296)), (271/2147483648), by norm_num⟩
  | 4 => ⟨((-691793751/4294967296), (435807129/2147483648)), (415/4294967296), by norm_num⟩
  | 5 => ⟨((842472639/8589934592), (-530729833/4294967296)), (507/8589934592), by norm_num⟩
  | 6 => ⟨((-427487809/8589934592), (538606295/8589934592)), (517/17179869184), by norm_num⟩
  | 7 => ⟨((743712129/34359738368), (-234256993/8589934592)), (113/8589934592), by norm_num⟩
  | 8 => ⟨((-283031033/34359738368), (713200671/68719476736)), (173/34359738368), by norm_num⟩
  | 9 => ⟨((191487629/68719476736), (-965046865/274877906944)), (235/137438953472), by norm_num⟩
  | 10 => ⟨((-932781413/1099511627776), (587621367/549755813888)), (287/549755813888), by norm_num⟩
  | 11 => ⟨((516340717/2199023255552), (-162638767/549755813888)), (319/2199023255552), by norm_num⟩
  | 12 => ⟨((-524003633/8796093022208), (330104917/4398046511104)), (325/8796093022208), by norm_num⟩
  | 13 => ⟨((245437049/17592186044416), (-38654301/2199023255552)), (153/17592186044416), by norm_num⟩
  | 14 => ⟨((-853986975/281474976710656), (268991741/70368744177664)), (535/281474976710656), by norm_num⟩
  | 15 => ⟨((693328669/1125899906842624), (-873548151/1125899906842624)), (437/1125899906842624), by norm_num⟩
  | 16 => ⟨((-65964209/562949953421312), (664884237/4503599627370496)), (335/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (2920037726783/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777913239186339/633825300114114700748351602688), (3452568767557/633825300114114700748351602688)), (23135/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236097409167061/4951760157141521099596496896), (485405934183/4951760157141521099596496896)), (208259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888494030531715/2475880078570760549798248448), (1031211084047/618970019642690137449562112)), (110663/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885080052987041/77371252455336267181195264), (2061800179677/77371252455336267181195264)), (221383/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48393345957595/302231454903657293676544), (1932277007521/4835703278458516698824704)), (207607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257942938902289/604462909807314587353088), (1690081947495/302231454903657293676544)), (181717/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471604341220425/18889465931478580854784), (343143166589/4722366482869645213696)), (295403/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296508141756149/4722366482869645213696), (4115552756799/4722366482869645213696)), (55413/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810014786074005/295147905179352825856), (5655368328347/590295810358705651712)), (304933/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821700708142831/73786976294838206464), (7063938502421/73786976294838206464)), (381409/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820660227820449/9223372036854775808), (3969843537799/4611686018427387904)), (107355/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49747108221403/36028797018963968), (3965320049469/576460752303423488)), (214919/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192760742903967/144115188075855872), (3464571408783/72057594037927936)), (376579/144115188075855872), by norm_num⟩
  | 4 => ⟨((93056534205021/2251799813685248), (324168941349/1125899906842624)), (282905/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485836714719733/9007199254740992), (6465638955871/4503599627370496)), (708915/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110545815674143/2251799813685248), (25756354149731/4503599627370496)), (355699/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205783380915349/2251799813685248), (19184928785345/1125899906842624)), (2146647/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159953237417163/2251799813685248), (18921499111701/562949953421312)), (135729/70368744177664), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159953237417163/2251799813685248), (18921499111701/562949953421312)), (517765045434451081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1034654499359075/1125899906842624), (145197820924297/2251799813685248)), (8624315/2251799813685248), by norm_num⟩
  | 2 => ⟨((236530646456609/281474976710656), (266861339633197/2251799813685248)), (16962969/2251799813685248), by norm_num⟩
  | 3 => ⟨((194809547107865/281474976710656), (112125216094435/562949953421312)), (32529409/2251799813685248), by norm_num⟩
  | 4 => ⟨((61830973449367/140737488355328), (620817177341689/2251799813685248)), (57985425/2251799813685248), by norm_num⟩
  | 5 => ⟨((131737236099329/1125899906842624), (272747018990493/1125899906842624)), (20730767/562949953421312), by norm_num⟩
  | 6 => ⟨((-202633419352729/4503599627370496), (510609345896835/9007199254740992)), (476647375/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1227363145/16777216)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile028Terms2

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile053Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨53,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77087/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77087/2560))
  have he : value ((69/80), (77087/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-715655399/268435456), (-24985383951/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((488701009307503/18014398509481984), (18019259274007/281474976710656)), (10962795/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2881232389/34359738368), (-13598216649/68719476736)), (65/17179869184), by norm_num⟩
  | 2 => ⟨((556625727/4294967296), (5254083119/17179869184)), (101/17179869184), by norm_num⟩
  | 3 => ⟨((-9176286681/68719476736), (-21654125299/68719476736)), (419/68719476736), by norm_num⟩
  | 4 => ⟨((1772768231/17179869184), (16733455147/68719476736)), (163/34359738368), by norm_num⟩
  | 5 => ⟨((-8767522979/137438953472), (-5172382025/34359738368)), (405/137438953472), by norm_num⟩
  | 6 => ⟨((4516797623/137438953472), (666168851/8589934592)), (419/274877906944), by norm_num⟩
  | 7 => ⟨((-7978064689/549755813888), (-18826570967/549755813888)), (93/137438953472), by norm_num⟩
  | 8 => ⟨((3082567081/549755813888), (14548432527/1099511627776)), (289/1099511627776), by norm_num⟩
  | 9 => ⟨((-8469640633/4398046511104), (-19986587809/4398046511104)), (399/4398046511104), by norm_num⟩
  | 10 => ⟨((654500469/1099511627776), (12355878283/8796093022208)), (31/1099511627776), by norm_num⟩
  | 11 => ⟨((-735668631/4398046511104), (-13888197935/35184372088832)), (281/35184372088832), by norm_num⟩
  | 12 => ⟨((6063954587/140737488355328), (7154834903/70368744177664)), (291/140737488355328), by norm_num⟩
  | 13 => ⟨((-5767366481/562949953421312), (-6804891825/281474976710656)), (139/281474976710656), by norm_num⟩
  | 14 => ⟨((10186956935/4503599627370496), (6009774149/1125899906842624)), (493/4503599627370496), by norm_num⟩
  | 15 => ⟨((-4198442181/9007199254740992), (-19814898165/18014398509481984)), (409/18014398509481984), by norm_num⟩
  | 16 => ⟨((3244390755/36028797018963968), (15312172859/72057594037927936)), (159/36028797018963968), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (1524018079083/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777856095320653/633825300114114700748351602688), (1801835787367/633825300114114700748351602688)), (2887/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472178814359875/9903520314283042199192993792), (1013299141247/19807040628566084398385987584)), (12993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944213187232831/1237940039285380274899124224), (2152675237147/2475880078570760549798248448)), (13807/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442523213850549/38685626227668133590597632), (1076008463811/77371252455336267181195264)), (13809/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548524453733693/9671406556917033397649408), (2016816682623/9671406556917033397649408)), (3237/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628944289615253/302231454903657293676544), (1764015710557/604462909807314587353088)), (11331/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943164918047431/37778931862957161709568), (1432607877413/37778931862957161709568)), (1151/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296443199333963/4722366482869645213696), (2147766400613/4722366482869645213696)), (1727/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404985354772039/147573952589676412928), (2951318695183/590295810358705651712)), (19001/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821592228347627/73786976294838206464), (3686360299499/73786976294838206464)), (1485/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910270268570523/4611686018427387904), (4143325133363/9223372036854775808)), (6685/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591790702382169/1152921504606846976), (517317807769/144115188075855872)), (13377/576460752303423488), by norm_num⟩
  | 5 => ⟨((596330932372847/72057594037927936), (1807925565569/72057594037927936)), (23425/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488762783079377/36028797018963968), (2706523541039/18014398509481984)), (1099/1125899906842624), by norm_num⟩
  | 3 => ⟨((1485670928172405/9007199254740992), (6747571186047/9007199254740992)), (22007/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220794118488885/4503599627370496), (13439085695911/4503599627370496)), (44095/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205421579177133/2251799813685248), (20019032580759/2251799813685248)), (132693/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079781713055965/1125899906842624), (39482944459949/2251799813685248)), (267029/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079781713055965/1125899906842624), (39482944459949/2251799813685248)), (1018634804732512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070412858266955/2251799813685248), (75731352576471/2251799813685248)), (130387/562949953421312), by norm_num⟩
  | 2 => ⟨((950545012904165/1125899906842624), (8703880180387/140737488355328)), (497077/1125899906842624), by norm_num⟩
  | 3 => ⟨((24943584409757/35184372088832), (117572510282319/1125899906842624)), (1801603/2251799813685248), by norm_num⟩
  | 4 => ⟨((1107188093580097/2251799813685248), (83351774108395/562949953421312)), (1465361/1125899906842624), by norm_num⟩
  | 5 => ⟨((123757135940623/562949953421312), (655732121910495/4503599627370496)), (7499751/4503599627370496), by norm_num⟩
  | 6 => ⟨((488701009307503/18014398509481984), (18019259274007/281474976710656)), (10962795/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-24985383951/268435456)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-725947119/268435456), (-25344694563/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((594155334931087/9007199254740992), (-50556698624589/4503599627370496)), (10992095/18014398509481984), by norm_num⟩
  | 1 => ⟨((-28426675659/137438953472), (2418826845/68719476736)), (265/137438953472), by norm_num⟩
  | 2 => ⟨((5570729819/17179869184), (-3792108791/68719476736)), (105/34359738368), by norm_num⟩
  | 3 => ⟨((-23289321501/68719476736), (3963378393/68719476736)), (221/68719476736), by norm_num⟩
  | 4 => ⟨((18255883215/68719476736), (-3106787507/68719476736)), (175/68719476736), by norm_num⟩
  | 5 => ⟨((-22896486491/137438953472), (3896525703/137438953472)), (111/68719476736), by norm_num⟩
  | 6 => ⟨((23930600319/274877906944), (-1018127817/68719476736)), (117/137438953472), by norm_num⟩
  | 7 => ⟨((-21438359681/549755813888), (3648381579/549755813888)), (53/137438953472), by norm_num⟩
  | 8 => ⟨((8402481597/549755813888), (-2859869835/1099511627776)), (21/137438953472), by norm_num⟩
  | 9 => ⟨((-23418606619/4398046511104), (3985380145/4398046511104)), (59/1099511627776), by norm_num⟩
  | 10 => ⟨((114732665/68719476736), (-2499227279/8796093022208)), (75/4398046511104), by norm_num⟩
  | 11 => ⟨((-8372214865/17592186044416), (1424784123/17592186044416)), (173/35184372088832), by norm_num⟩
  | 12 => ⟨((8750343761/70368744177664), (-2978268251/140737488355328)), (91/70368744177664), by norm_num⟩
  | 13 => ⟨((-4221023423/140737488355328), (2873336269/562949953421312)), (177/562949953421312), by norm_num⟩
  | 14 => ⟨((59084797/8796093022208), (-321761759/281474976710656)), (5/70368744177664), by norm_num⟩
  | 15 => ⟨((-25294170691/18014398509481984), (4304563773/18014398509481984)), (135/9007199254740992), by norm_num⟩
  | 16 => ⟨((9913715737/36028797018963968), (-3374233703/72057594037927936)), (213/72057594037927936), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (-219574948241/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888899378315883/316912650057057350374175801344), (-32448183105/79228162514264337593543950336)), (11529/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944325430005181/19807040628566084398385987584), (-291965749817/39614081257132168796771975168)), (12971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888358096466181/2475880078570760549798248448), (-310128088747/2475880078570760549798248448)), (6891/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770024739526747/154742504910672534362390528), (-77507982317/38685626227668133590597632)), (6891/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548460767226055/9671406556917033397649408), (-145276403195/4835703278458516698824704)), (12921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257833025514157/604462909807314587353088), (-127065812869/302231454903657293676544)), (5653/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471559970862623/18889465931478580854784), (-206386296431/37778931862957161709568)), (4593/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((10127937628233/36893488147419103232), (-77353039689/1180591620717411303424)), (3445/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619849499525885/590295810358705651712), (-425170067399/590295810358705651712)), (4737/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910739006648879/36893488147419103232), (-132763859461/18446744073709551616)), (23685/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820412984598279/9223372036854775808), (-149219519227/2305843009213693952)), (3331/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591664321579983/1152921504606846976), (-596179766169/1152921504606846976)), (13325/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192552596327677/144115188075855872), (-520872797977/144115188075855872)), (23321/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488601501477887/36028797018963968), (-779742953309/36028797018963968)), (34985/36028797018963968), by norm_num⟩
  | 3 => ⟨((371368473448915/2251799813685248), (-30373248245/281474976710656)), (10935/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110206838092175/2251799813685248), (-1935708300967/4503599627370496)), (87505/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204884715480571/2251799813685248), (-2883199523827/2251799813685248)), (65661/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158623308596785/2251799813685248), (-5685461504621/2251799813685248)), (131457/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158623308596785/2251799813685248), (-5685461504621/2251799813685248)), (501468662742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069287969395011/2251799813685248), (-5450204609405/1125899906842624)), (252699/1125899906842624), by norm_num⟩
  | 2 => ⟨((118844764067699/140737488355328), (-20033828514313/2251799813685248)), (933763/2251799813685248), by norm_num⟩
  | 3 => ⟨((1605543520341995/2251799813685248), (-8458711502457/562949953421312)), (1593635/2251799813685248), by norm_num⟩
  | 4 => ⟨((572125724331331/1125899906842624), (-12062199633089/562949953421312)), (1160215/1125899906842624), by norm_num⟩
  | 5 => ⟨((1160834478503489/4503599627370496), (-49035227093769/2251799813685248)), (2457691/2251799813685248), by norm_num⟩
  | 6 => ⟨((594155334931087/9007199254740992), (-50556698624589/4503599627370496)), (10992095/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-25344694563/268435456)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-735800759/268435456), (-6422177661/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((139874123770635/18014398509481984), (-1153500687740701/18014398509481984)), (22720461/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1695737819/68719476736), (27968500359/137438953472)), (553/137438953472), by norm_num⟩
  | 2 => ⟨((673643259/17179869184), (-5555337481/17179869184)), (441/68719476736), by norm_num⟩
  | 3 => ⟨((-1427249693/34359738368), (11770107707/34359738368)), (469/68719476736), by norm_num⟩
  | 4 => ⟨((2267938177/68719476736), (-18703017941/68719476736)), (187/34359738368), by norm_num⟩
  | 5 => ⟨((-720762961/34359738368), (23775679123/137438953472)), (477/137438953472), by norm_num⟩
  | 6 => ⟨((763541163/68719476736), (-6296699009/68719476736)), (507/274877906944), by norm_num⟩
  | 7 => ⟨((-2773228477/549755813888), (714687443/17179869184)), (463/549755813888), by norm_num⟩
  | 8 => ⟨((1101683673/549755813888), (-9085260663/549755813888)), (369/1099511627776), by norm_num⟩
  | 9 => ⟨((-1556093341/2199023255552), (12832643311/2199023255552)), (131/1099511627776), by norm_num⟩
  | 10 => ⟨((1978139361/8796093022208), (-16313132491/8796093022208)), (335/8796093022208), by norm_num⟩
  | 11 => ⟨((-2286048499/35184372088832), (4713092109/8796093022208)), (389/35184372088832), by norm_num⟩
  | 12 => ⟨((605432099/35184372088832), (-19971280573/140737488355328)), (207/70368744177664), by norm_num⟩
  | 13 => ⟨((-2368117909/562949953421312), (4882292671/140737488355328)), (203/281474976710656), by norm_num⟩
  | 14 => ⟨((2150287483/2251799813685248), (-8866393671/1125899906842624)), (185/1125899906842624), by norm_num⟩
  | 15 => ⟨((-3644655665/18014398509481984), (30056401459/18014398509481984)), (629/18014398509481984), by norm_num⟩
  | 16 => ⟨((1447863987/36028797018963968), (-11940107723/36028797018963968)), (251/36028797018963968), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-1888949634339/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111108724420761/39614081257132168796771975168), (-558253726467/158456325028528675187087900672)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888584169517433/39614081257132168796771975168), (-2511546537131/39614081257132168796771975168)), (12999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944143531627055/1237940039285380274899124224), (-2667772135219/2475880078570760549798248448)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769953510187013/154742504910672534362390528), (-333366650359/19342813113834066795298816)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387098445379711/2417851639229258349412352), (-624839712753/2417851639229258349412352)), (12955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257774205026881/604462909807314587353088), (-2186048349321/604462909807314587353088)), (5669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943071955306003/37778931862957161709568), (-3550659417725/75557863725914323419136)), (18429/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648151848186159/2361183241434822606848), (-2661534866749/4722366482869645213696)), (6913/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202468688390463/73786976294838206464), (-3657239952103/590295810358705651712)), (2377/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910676097860081/36893488147419103232), (-4567996859007/73786976294838206464)), (5945/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820270304936877/9223372036854775808), (-5134115288379/9223372036854775808)), (13383/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591520226816729/1152921504606846976), (-320501267065/72057594037927936)), (26783/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192424926232465/144115188075855872), (-2240084858049/72057594037927936)), (11727/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488406833983671/36028797018963968), (-1676645168669/9007199254740992)), (8805/9007199254740992), by norm_num⟩
  | 3 => ⟨((46413282882679/281474976710656), (-8359346272691/9007199254740992)), (44091/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219899578896459/4503599627370496), (-16647252470431/4503599627370496)), (88383/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204072908161117/2251799813685248), (-24792972055393/2251799813685248)), (133079/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078419639786397/1125899906842624), (-48878465218823/2251799813685248)), (268191/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078419639786397/1125899906842624), (-48878465218823/2251799813685248)), (1023067482955168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129051396611955/140737488355328), (-93634427952685/2251799813685248)), (262703/1125899906842624), by norm_num⟩
  | 2 => ⟨((944738490456171/1125899906842624), (-85859523567361/1125899906842624)), (503627/1125899906842624), by norm_num⟩
  | 3 => ⟨((1572358168221993/2251799813685248), (-18011102983787/140737488355328)), (1843991/2251799813685248), by norm_num⟩
  | 4 => ⟨((1061046296387645/2251799813685248), (-402450054014665/2251799813685248)), (1523587/1125899906842624), by norm_num⟩
  | 5 => ⟨((107009201178069/562949953421312), (-758536592281565/4503599627370496)), (7921715/4503599627370496), by norm_num⟩
  | 6 => ⟨((139874123770635/18014398509481984), (-1153500687740701/18014398509481984)), (22720461/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-6422177661/67108864)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-745252095/268435456), (-26018681267/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-251008541976067/4503599627370496), (-500240885738897/18014398509481984)), (12681201/9007199254740992), by norm_num⟩
  | 1 => ⟨((1541071563/8589934592), (6142476249/68719476736)), (157/34359738368), by norm_num⟩
  | 2 => ⟨((-9921035997/34359738368), (-9885934151/68719476736)), (507/68719476736), by norm_num⟩
  | 3 => ⟨((665303811/2147483648), (2651799537/17179869184)), (273/34359738368), by norm_num⟩
  | 4 => ⟨((-17132242827/68719476736), (-4267906711/34359738368)), (441/68719476736), by norm_num⟩
  | 5 => ⟨((2757328113/17179869184), (2747572347/34359738368)), (285/68719476736), by norm_num⟩
  | 6 => ⟨((-11833995739/137438953472), (-5896062803/137438953472)), (307/137438953472), by norm_num⟩
  | 7 => ⟨((21766950169/549755813888), (5422484005/274877906944)), (567/549755813888), by norm_num⟩
  | 8 => ⟨((-4379069355/274877906944), (-8727151337/1099511627776)), (229/549755813888), by norm_num⟩
  | 9 => ⟨((6264746881/1099511627776), (6242581435/2199023255552)), (329/2199023255552), by norm_num⟩
  | 10 => ⟨((-16132353827/8796093022208), (-4018818893/4398046511104)), (425/8796093022208), by norm_num⟩
  | 11 => ⟨((18882924993/35184372088832), (9408057439/35184372088832)), (499/35184372088832), by norm_num⟩
  | 12 => ⟨((-20260596921/140737488355328), (-1261807027/17592186044416)), (269/70368744177664), by norm_num⟩
  | 13 => ⟨((20066567885/562949953421312), (9997784947/562949953421312)), (535/562949953421312), by norm_num⟩
  | 14 => ⟨((-18454797215/2251799813685248), (-4597375467/1125899906842624)), (247/1125899906842624), by norm_num⟩
  | 15 => ⟨((15840986829/9007199254740992), (1973117433/2251799813685248)), (213/4503599627370496), by norm_num⟩
  | 16 => ⟨((-6373771193/18014398509481984), (-6351220005/36028797018963968)), (345/36028797018963968), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-3490167239025/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111104932348245/39614081257132168796771975168), (-4125648434435/633825300114114700748351602688)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888515575877883/39614081257132168796771975168), (-1160056184047/9903520314283042199192993792)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888213727852671/2475880078570760549798248448), (-1232210198753/618970019642690137449562112)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884939831955875/77371252455336267181195264), (-4927268491279/154742504910672534362390528)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774162004153577/4835703278458516698824704), (-4617644130291/9671406556917033397649408)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257712611672343/604462909807314587353088), (-4038769087051/604462909807314587353088)), (5685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235755350835151/9444732965739290427392), (-3279935289587/37778931862957161709568)), (18483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296226981669525/4722366482869645213696), (-4917166071179/4722366482869645213696)), (6935/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619642585554937/590295810358705651712), (-6756658149375/590295810358705651712)), (19083/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910608194596867/36893488147419103232), (-8439158745975/73786976294838206464)), (373/1152921504606846976), by norm_num⟩
  | 7 => ⟨((910057283047009/4611686018427387904), (-9484896937643/9223372036854775808)), (105/36028797018963968), by norm_num⟩
  | 6 => ⟨((397840200344041/288230376151711744), (-4736730261193/576460752303423488)), (26911/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298070323485813/36028797018963968), (-8276424911873/144115188075855872)), (23583/144115188075855872), by norm_num⟩
  | 4 => ⟨((186022893302125/4503599627370496), (-3097240894067/9007199254740992)), (8861/9007199254740992), by norm_num⟩
  | 3 => ⟨((185616386715165/1125899906842624), (-965084249435/562949953421312)), (44429/9007199254740992), by norm_num⟩
  | 2 => ⟨((554817222874191/1125899906842624), (-30748417082357/4503599627370496)), (22307/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203020916473521/2251799813685248), (-22893972435511/1125899906842624)), (134773/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077158608114761/1125899906842624), (-45121631264647/1125899906842624)), (273285/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077158608114761/1125899906842624), (-45121631264647/1125899906842624)), (1042499550826262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64294941894291/70368744177664), (-172673088374945/2251799813685248)), (272407/1125899906842624), by norm_num⟩
  | 2 => ⟨((466652905985785/562949953421312), (-157768996924899/1125899906842624)), (539567/1125899906842624), by norm_num⟩
  | 3 => ⟨((1503097526035231/2251799813685248), (-523125442622547/2251799813685248)), (261439/281474976710656), by norm_num⟩
  | 4 => ⟨((440901080990085/1125899906842624), (-698382292984721/2251799813685248)), (3763985/2251799813685248), by norm_num⟩
  | 5 => ⟨((257427169108753/4503599627370496), (-273485685583539/1125899906842624)), (10565399/4503599627370496), by norm_num⟩
  | 6 => ⟨((-251008541976067/4503599627370496), (-500240885738897/18014398509481984)), (12681201/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-26018681267/268435456)), (1/134217728), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-754332693/268435456), (-26335708481/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-204038606841809/4503599627370496), (89259153660555/2251799813685248)), (3118581/2251799813685248), by norm_num⟩
  | 1 => ⟨((10143699319/68719476736), (-8874967637/68719476736)), (311/68719476736), by norm_num⟩
  | 2 => ⟨((-16524575817/68719476736), (14457750667/68719476736)), (509/68719476736), by norm_num⟩
  | 3 => ⟨((17946221087/68719476736), (-15701582465/68719476736)), (555/68719476736), by norm_num⟩
  | 4 => ⟨((-14617630199/68719476736), (3197329467/17179869184)), (227/34359738368), by norm_num⟩
  | 5 => ⟨((9525130069/68719476736), (-4166883227/34359738368)), (297/68719476736), by norm_num⟩
  | 6 => ⟨((-10344597767/137438953472), (565671159/8589934592)), (81/34359738368), by norm_num⟩
  | 7 => ⟨((9629628049/274877906944), (-4212597131/137438953472)), (303/274877906944), by norm_num⟩
  | 8 => ⟨((-1960891113/137438953472), (13725048129/1099511627776)), (31/68719476736), by norm_num⟩
  | 9 => ⟨((11357817861/2199023255552), (-9937229287/2199023255552)), (361/2199023255552), by norm_num⟩
  | 10 => ⟨((-14801946821/8796093022208), (12950580935/8796093022208)), (59/1099511627776), by norm_num⟩
  | 11 => ⟨((17536789707/35184372088832), (-7671680529/17592186044416)), (561/35184372088832), by norm_num⟩
  | 12 => ⟨((-2380689743/17592186044416), (2082922981/17592186044416)), (153/35184372088832), by norm_num⟩
  | 13 => ⟨((4773241237/140737488355328), (-8352448189/281474976710656)), (309/281474976710656), by norm_num⟩
  | 14 => ⟨((-4443337357/562949953421312), (15550332873/2251799813685248)), (289/1125899906842624), by norm_num⟩
  | 15 => ⟨((15441943531/9007199254740992), (-844408095/562949953421312)), (63/1125899906842624), by norm_num⟩
  | 16 => ⟨((-6288917845/18014398509481984), (2751163091/9007199254740992)), (103/9007199254740992), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (1577987405699/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777628496430421/633825300114114700748351602688), (3730398543817/633825300114114700748351602688)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236057369675297/4951760157141521099596496896), (4195669399805/39614081257132168796771975168)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472038427618413/618970019642690137449562112), (557077473907/309485009821345068724781056)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769819803599905/154742504910672534362390528), (2227590729211/77371252455336267181195264)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96766753501369/604462909807314587353088), (65237576327/151115727451828646838272)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257663820037299/604462909807314587353088), (3651777099873/604462909807314587353088)), (11363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885963832373777/75557863725914323419136), (5931275520531/75557863725914323419136)), (2309/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296168023723453/4722366482869645213696), (2222976671013/2361183241434822606848)), (13861/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404890490271743/147573952589676412928), (763640025853/73786976294838206464)), (19069/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113819766979955/4611686018427387904), (3815152843569/36893488147419103232)), (23853/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820002844002797/9223372036854775808), (8575720175473/9223372036854775808)), (26857/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591250214514143/1152921504606846976), (1070657811025/144115188075855872)), (26885/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192185804260325/144115188075855872), (7482852788555/144115188075855872)), (5889/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488042451269331/36028797018963968), (700050494451/2251799813685248)), (35397/36028797018963968), by norm_num⟩
  | 3 => ⟨((742379825066391/4503599627370496), (13960008250953/9007199254740992)), (22179/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218939206280985/4503599627370496), (6949325921031/1125899906842624)), (89051/4503599627370496), by norm_num⟩
  | 1 => ⟨((550639783768959/562949953421312), (41390194678657/2251799813685248)), (134419/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076761547302895/1125899906842624), (81563463987483/2251799813685248)), (136111/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076761547302895/1125899906842624), (81563463987483/2251799813685248)), (519222263816451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2056581181061495/2251799813685248), (156007476602131/2251799813685248)), (135101/562949953421312), by norm_num⟩
  | 2 => ⟨((58358704279345/70368744177664), (17810311030699/140737488355328)), (1061989/2251799813685248), by norm_num⟩
  | 3 => ⟨((378172054571619/562949953421312), (472658336804543/2251799813685248)), (1015131/1125899906842624), by norm_num⟩
  | 4 => ⟨((458482083940809/1125899906842624), (635033978610189/2251799813685248)), (3580047/2251799813685248), by norm_num⟩
  | 5 => ⟨((388627024951431/4503599627370496), (1034378633897939/4503599627370496)), (9869841/4503599627370496), by norm_num⟩
  | 6 => ⟨((-204038606841809/4503599627370496), (89259153660555/2251799813685248)), (3118581/2251799813685248), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-26335708481/268435456)), (1/134217728), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-763070545/268435456), (-6660192377/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((147280301893775/9007199254740992), (1007532130946455/18014398509481984)), (19351721/18014398509481984), by norm_num⟩
  | 1 => ⟨((-7406797007/137438953472), (-3166829625/17179869184)), (489/137438953472), by norm_num⟩
  | 2 => ⟨((6102898659/68719476736), (20874707653/68719476736)), (405/68719476736), by norm_num⟩
  | 3 => ⟨((-6704719463/68719476736), (-11466605175/34359738368)), (447/68719476736), by norm_num⟩
  | 4 => ⟨((1381103849/17179869184), (1181001877/4294967296)), (185/34359738368), by norm_num⟩
  | 5 => ⟨((-3641514385/68719476736), (-778477905/4294967296)), (245/68719476736), by norm_num⟩
  | 6 => ⟨((4000612453/137438953472), (6841963143/68719476736)), (271/137438953472), by norm_num⟩
  | 7 => ⟨((-3767247431/274877906944), (-25771422129/549755813888)), (513/549755813888), by norm_num⟩
  | 8 => ⟨((6208116483/1099511627776), (10617300393/549755813888)), (425/1099511627776), by norm_num⟩
  | 9 => ⟨((-1136718843/549755813888), (-15552395579/2199023255552)), (313/2199023255552), by norm_num⟩
  | 10 => ⟨((2997151895/4398046511104), (10251631741/4398046511104)), (415/8796093022208), by norm_num⟩
  | 11 => ⟨((-3592044985/17592186044416), (-12286438483/17592186044416)), (125/8796093022208), by norm_num⟩
  | 12 => ⟨((1973132381/35184372088832), (13498032301/70368744177664)), (69/17592186044416), by norm_num⟩
  | 13 => ⟨((-4001921503/281474976710656), (-13688403839/281474976710656)), (281/281474976710656), by norm_num⟩
  | 14 => ⟨((7536960243/2251799813685248), (25779854863/2251799813685248)), (133/562949953421312), by norm_num⟩
  | 15 => ⟨((-3312078857/4503599627370496), (-11328826141/4503599627370496)), (469/9007199254740992), by norm_num⟩
  | 16 => ⟨((682254475/4503599627370496), (9334490711/18014398509481984)), (97/9007199254740992), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (1675633675285/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888791870515677/316912650057057350374175801344), (990255877857/316912650057057350374175801344)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888408912428249/39614081257132168796771975168), (2227530367939/39614081257132168796771975168)), (12995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472025236905893/618970019642690137449562112), (18484882339/19342813113834066795298816)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884883750691409/77371252455336267181195264), (1182646746235/77371252455336267181195264)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548219511704541/9671406556917033397649408), (2216643318785/9671406556917033397649408)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257621832307681/604462909807314587353088), (1938743947095/604462909807314587353088)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471474129339363/18889465931478580854784), (1574462081689/37778931862957161709568)), (9211/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296118337142431/4722366482869645213696), (2360351008699/4722366482869645213696)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404873734919869/147573952589676412928), (1621651593945/295147905179352825856)), (297/9223372036854775808), by norm_num⟩
  | 8 => ⟨((910517219082191/36893488147419103232), (4050862409721/73786976294838206464)), (2971/9223372036854775808), by norm_num⟩
  | 7 => ⟨((56872295251167/288230376151711744), (4552732889103/9223372036854775808)), (26751/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591164144149739/1152921504606846976), (568391257393/144115188075855872)), (13383/576460752303423488), by norm_num⟩
  | 5 => ⟨((298028555813679/36028797018963968), (3972444301269/144115188075855872)), (23437/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487942514096333/36028797018963968), (5946099129075/36028797018963968)), (17595/18014398509481984), by norm_num⟩
  | 3 => ⟨((742323839310635/4503599627370496), (7410679790027/9007199254740992)), (44047/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109376936665147/2251799813685248), (461116299387/140737488355328)), (88271/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202376824869349/2251799813685248), (10985082901855/1125899906842624)), (132855/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153536241718147/2251799813685248), (21645360613371/1125899906842624)), (1045/8796093022208), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153536241718147/2251799813685248), (21645360613371/1125899906842624)), (3986358676132557/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((2058728413456197/2251799813685248), (20700804868469/562949953421312)), (521979/2251799813685248), by norm_num⟩
  | 2 => ⟨((939583146223695/1125899906842624), (37851797397907/562949953421312)), (496419/1125899906842624), by norm_num⟩
  | 3 => ⟨((779008372833275/1125899906842624), (126351945401905/1125899906842624)), (447649/562949953421312), by norm_num⟩
  | 4 => ⟨((262407531631537/562949953421312), (43711356042245/281474976710656)), (1439857/1125899906842624), by norm_num⟩
  | 5 => ⟨((108739652071585/562949953421312), (652004760201679/4503599627370496)), (7158087/4503599627370496), by norm_num⟩
  | 6 => ⟨((147280301893775/9007199254740992), (1007532130946455/18014398509481984)), (19351721/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-6660192377/67108864)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨53,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile053Terms3

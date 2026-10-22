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
namespace Reinmann.XiBand97.Tile011Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25029/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25029/1280))
  have he : value ((69/80), (25029/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-454787879/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-569562727152917/9007199254740992), (595747788461583/9007199254740992)), (37659297/2251799813685248), by norm_num⟩
  | 1 => ⟨((376501845/2147483648), (-787622261/4294967296)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((-1043884769/4294967296), (1091876299/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((964754379/4294967296), (-1009107971/4294967296)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-334358389/2147483648), (699460345/4294967296)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((741630639/8589934592), (-387863173/4294967296)), (205/8589934592), by norm_num⟩
  | 6 => ⟨((-685412249/17179869184), (716923373/17179869184)), (191/17179869184), by norm_num⟩
  | 7 => ⟨((4241889/268435456), (-567923903/34359738368)), (153/34359738368), by norm_num⟩
  | 8 => ⟨((-752704871/137438953472), (98413713/17179869184)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((463764675/274877906944), (-485085779/274877906944)), (133/274877906944), by norm_num⟩
  | 10 => ⟨((-514331483/1099511627776), (1050737/2147483648)), (297/2199023255552), by norm_num⟩
  | 11 => ⟨((1037112487/8796093022208), (-1084792667/8796093022208)), (151/4398046511104), by norm_num⟩
  | 12 => ⟨((-479247731/17592186044416), (1002561305/35184372088832)), (281/35184372088832), by norm_num⟩
  | 13 => ⟨((408848263/70368744177664), (-427644641/70368744177664)), (121/70368744177664), by norm_num⟩
  | 14 => ⟨((-323876595/281474976710656), (42345811/35184372088832)), (97/281474976710656), by norm_num⟩
  | 15 => ⟨((957841701/4503599627370496), (-1001877487/4503599627370496)), (289/4503599627370496), by norm_num⟩
  | 16 => ⟨((-663925275/18014398509481984), (694448555/18014398509481984)), (203/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (3039941038131/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778274009415861/633825300114114700748351602688), (1797865785677/316912650057057350374175801344)), (92555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889185017667683/39614081257132168796771975168), (4044344564203/39614081257132168796771975168)), (104147/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888924983641283/2475880078570760549798248448), (67126039799/38685626227668133590597632)), (55341/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442647722521707/38685626227668133590597632), (1073721518141/38685626227668133590597632)), (13839/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548990751235197/9671406556917033397649408), (2012600876915/4835703278458516698824704)), (6489/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258295979958017/604462909807314587353088), (3520797949487/604462909807314587353088)), (90877/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471747680053487/18889465931478580854784), (714868368529/9444732965739290427392)), (73867/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648468932014345/2361183241434822606848), (1071788739705/1180591620717411303424)), (110853/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620619962358469/590295810358705651712), (2945749846963/295147905179352825856)), (152507/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227804747423963/9223372036854775808), (7359369524177/73786976294838206464)), (190759/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821488673349273/9223372036854775808), (8272412722459/9223372036854775808)), (107389/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592734678702989/1152921504606846976), (8263821248105/1152921504606846976)), (214995/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193483174120245/144115188075855872), (3610593227287/72057594037927936)), (94183/72057594037927936), by norm_num⟩
  | 4 => ⟨((372496358052221/9007199254740992), (5406243041117/18014398509481984)), (141519/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487182994328629/9007199254740992), (13481890316345/9007199254740992)), (354657/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223769738017815/4503599627370496), (26862814790453/4503599627370496)), (355947/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104882252308107/1125899906842624), (40042458480999/2251799813685248)), (1074313/2251799813685248), by norm_num⟩
  | 0 => ⟨((135485744470533/140737488355328), (39540883120191/1125899906842624)), (2174613/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((135485744470533/140737488355328), (39540883120191/1125899906842624)), (8295490273482512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084102283932565/2251799813685248), (76130760171529/1125899906842624)), (2169837/1125899906842624), by norm_num⟩
  | 2 => ⟨((1918598062340739/2251799813685248), (140922199377341/1125899906842624)), (2154963/562949953421312), by norm_num⟩
  | 3 => ⟨((12495498593155/17592186044416), (240139515975601/1125899906842624)), (16846515/2251799813685248), by norm_num⟩
  | 4 => ⟨((129201572063741/281474976710656), (682271771446277/2251799813685248)), (15558997/1125899906842624), by norm_num⟩
  | 5 => ⟨((535447409261859/4503599627370496), (1252695162827029/4503599627370496)), (11856045/562949953421312), by norm_num⟩
  | 6 => ⟨((-569562727152917/9007199254740992), (595747788461583/9007199254740992)), (37659297/2251799813685248), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-454787879/8388608)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-464732139/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((641507766598341/18014398509481984), (356714621301111/4503599627370496)), (216213505/18014398509481984), by norm_num⟩
  | 1 => ⟨((-216666265/2147483648), (-963829637/4294967296)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((613861753/4294967296), (1365367495/4294967296)), (53/1073741824), by norm_num⟩
  | 3 => ⟨((-289866885/2147483648), (-20147799/67108864)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((410627363/4294967296), (57083013/268435456)), (145/4294967296), by norm_num⟩
  | 5 => ⟨((-232678985/4294967296), (-1035061467/8589934592)), (83/4294967296), by norm_num⟩
  | 6 => ⟨((439486137/17179869184), (977516653/17179869184)), (159/17179869184), by norm_num⟩
  | 7 => ⟨((-355759425/34359738368), (-791289493/34359738368)), (65/17179869184), by norm_num⟩
  | 8 => ⟨((503971175/137438953472), (1120945975/137438953472)), (93/68719476736), by norm_num⟩
  | 9 => ⟨((-158650873/137438953472), (-352875455/137438953472)), (237/549755813888), by norm_num⟩
  | 10 => ⟨((44949177/137438953472), (399908579/549755813888)), (17/137438953472), by norm_num⟩
  | 11 => ⟨((-723583/8589934592), (-103002393/549755813888)), (71/2199023255552), by norm_num⟩
  | 12 => ⟨((174938881/8796093022208), (778207345/17592186044416)), (17/2199023255552), by norm_num⟩
  | 13 => ⟨((-610017443/140737488355328), (-1356816883/140737488355328)), (15/8796093022208), by norm_num⟩
  | 14 => ⟨((493802731/562949953421312), (1098329057/562949953421312)), (49/140737488355328), by norm_num⟩
  | 15 => ⟨((-373079597/2251799813685248), (-414906739/1125899906842624)), (75/1125899906842624), by norm_num⟩
  | 16 => ⟨((264253523/9007199254740992), (587759655/9007199254740992)), (215/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (1495762441111/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778198698931869/633825300114114700748351602688), (1769079002951/633825300114114700748351602688)), (92375/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944550301990429/19807040628566084398385987584), (1989791370569/39614081257132168796771975168)), (103933/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944417851553957/1237940039285380274899124224), (1056813193551/1237940039285380274899124224)), (55221/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770502069263487/154742504910672534362390528), (2113033819439/154742504910672534362390528)), (13807/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548907969809231/9671406556917033397649408), (990169910305/4835703278458516698824704)), (6473/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258224033916923/604462909807314587353088), (216521025405/75557863725914323419136)), (45319/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235859340190041/9444732965739290427392), (1406797107121/37778931862957161709568)), (147315/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324212915900629/1180591620717411303424), (2109164455003/4722366482869645213696)), (6907/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810251366469887/295147905179352825856), (2898426392459/590295810358705651712)), (151995/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227786673020317/9223372036854775808), (226282662367/4611686018427387904)), (23757/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821328668945587/9223372036854775808), (508704863081/1152921504606846976)), (213899/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398144499813003/288230376151711744), (2032665893393/576460752303423488)), (107003/576460752303423488), by norm_num⟩
  | 5 => ⟨((298337452783017/36028797018963968), (444040689105/18014398509481984)), (11711/9007199254740992), by norm_num⟩
  | 4 => ⟨((372448207056295/9007199254740992), (5318822918889/36028797018963968)), (140653/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486955209552445/9007199254740992), (6631646304051/9007199254740992)), (352055/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223352876902211/4503599627370496), (1651596677523/562949953421312)), (352693/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209235278685587/2251799813685248), (19693308593631/2251799813685248)), (1061277/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167093508578779/2251799813685248), (38885881439339/2251799813685248)), (266927/281474976710656), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167093508578779/2251799813685248), (38885881439339/2251799813685248)), (1018245698095226199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2084902101250993/2251799813685248), (2338944072937/70368744177664)), (4183929/2251799813685248), by norm_num⟩
  | 2 => ⟨((1927886657693033/2251799813685248), (138597596684773/2251799813685248)), (8025789/2251799813685248), by norm_num⟩
  | 3 => ⟨((25656821605491/35184372088832), (237321680029451/2251799813685248)), (3682647/562949953421312), by norm_num⟩
  | 4 => ⟨((18318420109145/35184372088832), (173057515201863/1125899906842624)), (24588379/2251799813685248), by norm_num⟩
  | 5 => ⟨((1114376715685125/4503599627370496), (90100805508441/562949953421312)), (66324377/4503599627370496), by norm_num⟩
  | 6 => ⟨((641507766598341/18014398509481984), (356714621301111/4503599627370496)), (216213505/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-464732139/8388608)), (1/16777216), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1896431347/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((744241271841917/9007199254740992), (45575755356643/18014398509481984)), (23787757/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2051481203/8589934592), (-62814177/8589934592)), (67/4294967296), by norm_num⟩
  | 2 => ⟨((1482385833/4294967296), (45389081/4294967296)), (99/4294967296), by norm_num⟩
  | 3 => ⟨((-714107691/2147483648), (-43730439/4294967296)), (97/4294967296), by norm_num⟩
  | 4 => ⟨((2064036703/8589934592), (63198613/8589934592)), (143/8589934592), by norm_num⟩
  | 5 => ⟨((-1193166679/8589934592), (-36533497/8589934592)), (21/2147483648), by norm_num⟩
  | 6 => ⟨((1149565091/17179869184), (35198463/17179869184)), (83/17179869184), by norm_num⟩
  | 7 => ⟨((-949334421/34359738368), (-58135225/68719476736)), (139/68719476736), by norm_num⟩
  | 8 => ⟨((342991175/34359738368), (42008103/137438953472)), (51/68719476736), by norm_num⟩
  | 9 => ⟨((-1762439121/549755813888), (-53964015/549755813888)), (133/549755813888), by norm_num⟩
  | 10 => ⟨((2037641705/2199023255552), (31195213/1099511627776)), (39/549755813888), by norm_num⟩
  | 11 => ⟨((-1070825825/4398046511104), (-16393775/2199023255552)), (83/4398046511104), by norm_num⟩
  | 12 => ⟨((2063389815/35184372088832), (31589403/17592186044416)), (81/17592186044416), by norm_num⟩
  | 13 => ⟨((-917532869/70368744177664), (-56187765/140737488355328)), (73/70368744177664), by norm_num⟩
  | 14 => ⟨((757717455/281474976710656), (2900063/35184372088832)), (123/562949953421312), by norm_num⟩
  | 15 => ⟨((-292011351/562949953421312), (-17882155/1125899906842624)), (3/70368744177664), by norm_num⟩
  | 16 => ⟨((422010681/4503599627370496), (12921519/4503599627370496)), (141/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (39872128741/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778124426213507/633825300114114700748351602688), (47154014111/633825300114114700748351602688)), (92205/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236127144769977/4951760157141521099596496896), (53036841117/39614081257132168796771975168)), (25933/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472186796929401/618970019642690137449562112), (3521082579/154742504910672534362390528)), (110215/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885206858867127/77371252455336267181195264), (56321216241/154742504910672534362390528)), (13777/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96801582139551/604462909807314587353088), (52784035155/9671406556917033397649408)), (103327/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258151884134505/604462909807314587353088), (23084466513/302231454903657293676544)), (90413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378901899811/37778931862957161709568), (74992473493/75557863725914323419136)), (18365/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324191064997793/1180591620717411303424), (56216333351/4722366482869645213696)), (110191/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620383015040077/590295810358705651712), (77251952159/590295810358705651712)), (75757/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455536107236655/18446744073709551616), (6031045745/4611686018427387904)), (94697/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821162044519965/9223372036854775808), (13558139983/1152921504606846976)), (13317/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592412560280997/1152921504606846976), (27087028641/288230376151711744)), (213075/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149150797816385/18014398509481984), (94673139759/144115188075855872)), (186445/144115188075855872), by norm_num⟩
  | 4 => ⟨((46549385577871/1125899906842624), (70873607133/18014398509481984)), (69919/9007199254740992), by norm_num⟩
  | 3 => ⟨((185836777857085/1125899906842624), (176725606867/9007199254740992)), (349611/9007199254740992), by norm_num⟩
  | 2 => ⟨((277855588729947/562949953421312), (352079796331/4503599627370496)), (87409/562949953421312), by norm_num⟩
  | 1 => ⟨((2208507299563547/2251799813685248), (262352234067/1125899906842624)), (262261/562949953421312), by norm_num⟩
  | 0 => ⟨((2165773177637495/2251799813685248), (1035827637931/2251799813685248)), (2098687/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165773177637495/2251799813685248), (1035827637931/2251799813685248)), (8005855568892668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((260379072971335/281474976710656), (996255395907/1125899906842624)), (504869/281474976710656), by norm_num⟩
  | 2 => ⟨((30108004804235/35184372088832), (1843176679223/1125899906842624)), (467477/140737488355328), by norm_num⟩
  | 3 => ⟨((1648893222619867/2251799813685248), (3154489849811/1125899906842624)), (6412723/1125899906842624), by norm_num⟩
  | 4 => ⟨((1207393765579603/2251799813685248), (9239572545597/2251799813685248)), (589215/70368744177664), by norm_num⟩
  | 5 => ⟨((647355207421393/2251799813685248), (19816685693595/4503599627370496)), (5093587/562949953421312), by norm_num⟩
  | 6 => ⟨((744241271841917/9007199254740992), (45575755356643/18014398509481984)), (23787757/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1896431347/33554432)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-241488243/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((183961614711831/4503599627370496), (-1216021253161421/18014398509481984)), (92860271/9007199254740992), by norm_num⟩
  | 1 => ⟨((-258285403/2147483648), (213414453/1073741824)), (133/4294967296), by norm_num⟩
  | 2 => ⟨((95063201/536870912), (-314192917/1073741824)), (99/2147483648), by norm_num⟩
  | 3 => ⟨((-746420785/4294967296), (1233495829/4294967296)), (49/1073741824), by norm_num⟩
  | 4 => ⟨((274723807/2147483648), (-226997075/1073741824)), (73/2147483648), by norm_num⟩
  | 5 => ⟨((-647125989/8589934592), (1069406457/8589934592)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((635140995/17179869184), (-1049600685/17179869184)), (173/17179869184), by norm_num⟩
  | 7 => ⟨((-133580993/8589934592), (882995763/34359738368)), (37/8589934592), by norm_num⟩
  | 8 => ⟨((786642165/137438953472), (-1299963571/137438953472)), (55/34359738368), by norm_num⟩
  | 9 => ⟨((-514715523/274877906944), (850591869/274877906944)), (73/137438953472), by norm_num⟩
  | 10 => ⟨((151554845/274877906944), (-500903171/549755813888)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((-162270543/1099511627776), (1072639143/4398046511104)), (47/1099511627776), by norm_num⟩
  | 12 => ⟨((637060949/17592186044416), (-1052773501/17592186044416)), (93/8796093022208), by norm_num⟩
  | 13 => ⟨((-577165259/70368744177664), (953793025/70368744177664)), (171/70368744177664), by norm_num⟩
  | 14 => ⟨((485550825/281474976710656), (-802395817/281474976710656)), (73/140737488355328), by norm_num⟩
  | 15 => ⟨((-381246607/1125899906842624), (1260056277/2251799813685248)), (29/281474976710656), by norm_num⟩
  | 16 => ⟨((561278685/9007199254740992), (-115942463/1125899906842624)), (173/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-1337281963805/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778051250961039/633825300114114700748351602688), (-790694630189/316912650057057350374175801344)), (23089/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888934779805933/39614081257132168796771975168), (-444667920605/9903520314283042199192993792)), (103911/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888659584520697/2475880078570760549798248448), (-944674606229/1237940039285380274899124224)), (110417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770326028928097/154742504910672534362390528), (-1888798827525/154742504910672534362390528)), (55215/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548743015098279/9671406556917033397649408), (-1770164331527/9671406556917033397649408)), (51771/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629039890802163/302231454903657293676544), (-387077365607/151115727451828646838272)), (45307/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886640467155463/75557863725914323419136), (-2514907775291/75557863725914323419136)), (18409/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162084513615401/590295810358705651712), (-1885223130899/4722366482869645213696)), (110477/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810130783117035/295147905179352825856), (-323828312845/73786976294838206464)), (151943/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227749032117747/9223372036854775808), (-404493982011/9223372036854775808)), (5937/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820990355672891/9223372036854775808), (-3637243068083/9223372036854775808)), (213809/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398060063449511/288230376151711744), (-3633243696099/1152921504606846976)), (213905/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193054921633733/144115188075855872), (-3174594559115/144115188075855872)), (187275/144115188075855872), by norm_num⟩
  | 4 => ⟨((372337941743435/9007199254740992), (-2376459258541/18014398509481984)), (281129/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486406105000195/9007199254740992), (-2962738174069/4503599627370496)), (175895/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222261310960997/4503599627370496), (-5902031557081/2251799813685248)), (704723/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103807228928841/1125899906842624), (-4397327488973/562949953421312)), (1059953/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081958751077273/1125899906842624), (-34714107678443/2251799813685248)), (1065723/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081958751077273/1125899906842624), (-34714107678443/2251799813685248)), (4065410618308639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2078929866859473/2251799813685248), (-16679649922815/562949953421312)), (65035/35184372088832), by norm_num⟩
  | 2 => ⟨((1917354284131349/2251799813685248), (-123193268540335/2251799813685248)), (7932059/2251799813685248), by norm_num⟩
  | 3 => ⟨((406460517406247/562949953421312), (-209792309046679/2251799813685248)), (14375829/2251799813685248), by norm_num⟩
  | 4 => ⟨((577171559973905/1125899906842624), (-302948032821477/2251799813685248)), (11718967/1125899906842624), by norm_num⟩
  | 5 => ⟨((550995039807685/2251799813685248), (-310601302357223/2251799813685248)), (60673057/4503599627370496), by norm_num⟩
  | 6 => ⟨((183961614711831/4503599627370496), (-1216021253161421/18014398509481984)), (92860271/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-241488243/4194304)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1965560511/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-150557915783949/4503599627370496), (-1219191200139115/18014398509481984)), (243432359/18014398509481984), by norm_num⟩
  | 1 => ⟨((215068439/2147483648), (870792967/4294967296)), (11/268435456), by norm_num⟩
  | 2 => ⟨((-80535933/536870912), (-652165649/2147483648)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((643370917/4294967296), (325618947/1073741824)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((-481841755/4294967296), (-975467189/4294967296)), (203/4294967296), by norm_num⟩
  | 5 => ⟨((577387559/8589934592), (146111927/1073741824)), (245/8589934592), by norm_num⟩
  | 6 => ⟨((-288283091/8589934592), (-583616287/8589934592)), (247/17179869184), by norm_num⟩
  | 7 => ⟨((123374137/8589934592), (499530899/17179869184)), (213/34359738368), by norm_num⟩
  | 8 => ⟨((-92398971/17179869184), (-374115209/34359738368)), (161/68719476736), by norm_num⟩
  | 9 => ⟨((492093475/274877906944), (498110669/137438953472)), (217/274877906944), by norm_num⟩
  | 10 => ⟨((-294836061/549755813888), (-596882483/549755813888)), (131/549755813888), by norm_num⟩
  | 11 => ⟨((321181783/2199023255552), (1300436449/4398046511104)), (9/137438953472), by norm_num⟩
  | 12 => ⟨((-641449755/17592186044416), (-81161655/1099511627776)), (145/8796093022208), by norm_num⟩
  | 13 => ⟨((591265149/70368744177664), (598494989/35184372088832)), (269/70368744177664), by norm_num⟩
  | 14 => ⟨((-126519435/70368744177664), (-256132965/70368744177664)), (29/35184372088832), by norm_num⟩
  | 15 => ⟨((404286245/1125899906842624), (818459509/1125899906842624)), (187/1125899906842624), by norm_num⟩
  | 16 => ⟨((-151391669/2251799813685248), (-1225942783/9007199254740992)), (141/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-2643780940435/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777979206496885/633825300114114700748351602688), (-781536992245/158456325028528675187087900672)), (92509/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944426766351831/19807040628566084398385987584), (-879030677041/9903520314283042199192993792)), (26023/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888572994916923/2475880078570760549798248448), (-1867447553671/1237940039285380274899124224)), (27655/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770239142040761/154742504910672534362390528), (-3733787052785/154742504910672534362390528)), (55323/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774330621519863/4835703278458516698824704), (-3499248424695/9671406556917033397649408)), (51879/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258007915746469/604462909807314587353088), (-3060665851147/604462909807314587353088)), (1419/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1886523094563075/75557863725914323419136), (-1242844229447/18889465931478580854784)), (147627/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296587563353269/4722366482869645213696), (-1863302059795/2361183241434822606848)), (55383/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620138978544023/590295810358705651712), (-5120948399577/590295810358705651712)), (19047/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821837768082637/73786976294838206464), (-3198245002489/36893488147419103232)), (190579/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910407417222299/4611686018427387904), (-7189599665677/9223372036854775808)), (26819/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592062585977627/1152921504606846976), (-3590771123603/576460752303423488)), (107371/576460752303423488), by norm_num⟩
  | 5 => ⟨((298224263554413/36028797018963968), (-3137397292251/72057594037927936)), (11757/9007199254740992), by norm_num⟩
  | 4 => ⟨((744555083388507/18014398509481984), (-9394106380663/36028797018963968)), (282595/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486095744701419/9007199254740992), (-11711037911625/9007199254740992)), (353991/9007199254740992), by norm_num⟩
  | 2 => ⟨((555403915760685/1125899906842624), (-23327508606519/4503599627370496)), (355115/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206584200550857/2251799813685248), (-34755606702921/2251799813685248)), (1070983/2251799813685248), by norm_num⟩
  | 0 => ⟨((540403256654611/562949953421312), (-68573150934413/2251799813685248)), (2164613/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540403256654611/562949953421312), (-68573150934413/2251799813685248)), (8257343300826262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072950078176861/2251799813685248), (-131653458211733/2251799813685248)), (4287673/2251799813685248), by norm_num⟩
  | 2 => ⟨((475152072527057/562949953421312), (-15149606374513/140737488355328)), (8395613/2251799813685248), by norm_num⟩
  | 3 => ⟨((394524098464037/562949953421312), (-409179782924353/2251799813685248)), (15979943/2251799813685248), by norm_num⟩
  | 4 => ⟨((257900382555105/562949953421312), (-573519134291945/2251799813685248)), (7051373/562949953421312), by norm_num⟩
  | 5 => ⟨((653057625536251/4503599627370496), (-525484737098357/2251799813685248)), (5026337/281474976710656), by norm_num⟩
  | 6 => ⟨((-150557915783949/4503599627370496), (-1219191200139115/18014398509481984)), (243432359/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1965560511/33554432)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-1997572725/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1287553354667167/18014398509481984), (-205082712315225/18014398509481984)), (6939515/562949953421312), by norm_num⟩
  | 1 => ⟨((934597273/4294967296), (148863535/4294967296)), (163/4294967296), by norm_num⟩
  | 2 => ⟨((-11114853/33554432), (-113304593/2147483648)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((721907613/2147483648), (114986125/2147483648)), (1/16777216), by norm_num⟩
  | 4 => ⟨((-1098931963/4294967296), (-175038919/4294967296)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((167286151/1073741824), (213163967/8589934592)), (241/8589934592), by norm_num⟩
  | 6 => ⟨((-339537627/4294967296), (-108163747/8589934592)), (247/17179869184), by norm_num⟩
  | 7 => ⟨((1181405627/34359738368), (188175403/34359738368)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((-899203985/68719476736), (-143226059/68719476736)), (83/34359738368), by norm_num⟩
  | 9 => ⟨((1216731871/274877906944), (24225275/34359738368)), (227/274877906944), by norm_num⟩
  | 10 => ⟨((-1481746993/1099511627776), (-236014059/1099511627776)), (139/549755813888), by norm_num⟩
  | 11 => ⟨((410110179/1099511627776), (261290945/4398046511104)), (155/2199023255552), by norm_num⟩
  | 12 => ⟨((-1664786189/17592186044416), (-265168715/17592186044416)), (317/17592186044416), by norm_num⟩
  | 13 => ⟨((1559531971/70368744177664), (62100931/17592186044416)), (299/70368744177664), by norm_num⟩
  | 14 => ⟨((-1356580023/281474976710656), (-108038673/140737488355328)), (131/140737488355328), by norm_num⟩
  | 15 => ⟨((550685109/562949953421312), (21928411/140737488355328)), (215/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1676573171/9007199254740992), (-267046157/9007199254740992)), (165/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-485815296717/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222238538425805/79228162514264337593543950336), (-4595312464477/633825300114114700748351602688)), (92653/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888773454785849/39614081257132168796771975168), (-2584262198061/19807040628566084398385987584)), (13033/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888487486901225/2475880078570760549798248448), (-85782551801/38685626227668133590597632)), (55407/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770153156163023/154742504910672534362390528), (-1372106374087/38685626227668133590597632)), (27713/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387145030994323/2417851639229258349412352), (-5143637878079/9671406556917033397649408)), (25991/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628968214872137/302231454903657293676544), (-1124730644125/151115727451828646838272)), (91009/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943202990267767/37778931862957161709568), (-3653724548693/37778931862957161709568)), (147965/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296498898235569/4722366482869645213696), (-85589065913/73786976294838206464)), (1735/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1620015717818751/590295810358705651712), (-940893611755/73786976294838206464)), (38197/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821681676227455/73786976294838206464), (-9401905955109/73786976294838206464)), (95573/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820636464590837/9223372036854775808), (-10567482923535/9223372036854775808)), (215261/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591880766087847/1152921504606846976), (-10555414128577/1152921504606846976)), (53885/288230376151711744), by norm_num⟩
  | 5 => ⟨((298183522914945/36028797018963968), (-9222420699485/144115188075855872)), (188911/144115188075855872), by norm_num⟩
  | 4 => ⟨((93053625651729/2251799813685248), (-13806524570285/36028797018963968)), (283993/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485767114786833/9007199254740992), (-537836869753/281474976710656)), (178045/4503599627370496), by norm_num⟩
  | 2 => ⟨((555229587211395/1125899906842624), (-8569918526597/1125899906842624)), (357743/2251799813685248), by norm_num⟩
  | 1 => ⟨((34459983786235/35184372088832), (-12766411423985/562949953421312)), (270379/562949953421312), by norm_num⟩
  | 0 => ⟨((539732668589365/562949953421312), (-50360464542635/1125899906842624)), (1098165/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((539732668589365/562949953421312), (-50360464542635/1125899906842624)), (4189167027000045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((32271664168233/35184372088832), (-48283489062933/562949953421312)), (2203989/1125899906842624), by norm_num⟩
  | 2 => ⟨((469460103822137/562949953421312), (-354291056262247/2251799813685248)), (8842269/2251799813685248), by norm_num⟩
  | 3 => ⟨((188780239926059/281474976710656), (-295453468013081/1125899906842624)), (17530073/2251799813685248), by norm_num⟩
  | 4 => ⟨((214457301705413/562949953421312), (-99077682198071/281474976710656)), (32714537/2251799813685248), by norm_num⟩
  | 5 => ⟨((95587691586711/4503599627370496), (-1207805120397139/4503599627370496)), (23978033/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1287553354667167/18014398509481984), (-205082712315225/18014398509481984)), (6939515/562949953421312), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1997572725/33554432)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile011Terms2

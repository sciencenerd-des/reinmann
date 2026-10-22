/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile049Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨49,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15131/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15131/512))
  have he : value ((69/80), (15131/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-6130311281/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-303959668858733/4503599627370496), (4700772743401/281474976710656)), (27236501/4503599627370496), by norm_num⟩
  | 1 => ⟨((3584107363/17179869184), (-886858405/17179869184)), (323/17179869184), by norm_num⟩
  | 2 => ⟨((-692414251/2147483648), (685329245/8589934592)), (501/17179869184), by norm_num⟩
  | 3 => ⟨((2853709127/8589934592), (-1412254527/17179869184)), (259/8589934592), by norm_num⟩
  | 4 => ⟨((-4410468031/17179869184), (545667337/8589934592)), (201/8589934592), by norm_num⟩
  | 5 => ⟨((5453177569/34359738368), (-1349344723/34359738368)), (499/34359738368), by norm_num⟩
  | 6 => ⟨((-5618667791/68719476736), (1390293941/68719476736)), (129/17179869184), by norm_num⟩
  | 7 => ⟨((2481077239/68719476736), (-1227845027/137438953472)), (457/137438953472), by norm_num⟩
  | 8 => ⟨((-1917278769/137438953472), (237207569/68719476736)), (355/274877906944), by norm_num⟩
  | 9 => ⟨((1316975571/274877906944), (-1303499851/1099511627776)), (245/549755813888), by norm_num⟩
  | 10 => ⟨((-101770685/68719476736), (1611669351/4398046511104)), (19/137438953472), by norm_num⟩
  | 11 => ⟨((3660538273/8796093022208), (-905770615/8796093022208)), (343/8796093022208), by norm_num⟩
  | 12 => ⟨((-3771626401/35184372088832), (933258475/35184372088832)), (355/35184372088832), by norm_num⟩
  | 13 => ⟨((896789025/35184372088832), (-443806395/70368744177664)), (85/35184372088832), by norm_num⟩
  | 14 => ⟨((-1584007399/281474976710656), (1567799323/1125899906842624)), (603/1125899906842624), by norm_num⟩
  | 15 => ⟨((5222649725/4503599627370496), (-1292302471/4503599627370496)), (499/4503599627370496), by norm_num⟩
  | 16 => ⟨((-4035858005/18014398509481984), (499320225/9007199254740992)), (387/18014398509481984), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (944075297143/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888923572790789/316912650057057350374175801344), (2232347082621/316912650057057350374175801344)), (46321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888704699527653/39614081257132168796771975168), (2510799246181/19807040628566084398385987584)), (52125/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944207250451799/1237940039285380274899124224), (5333994862281/2475880078570760549798248448)), (55399/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110630015306029/9671406556917033397649408), (1333089987847/38685626227668133590597632)), (55417/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548511849023461/9671406556917033397649408), (4997350795139/9671406556917033397649408)), (25987/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257876768469735/604462909807314587353088), (1092736443337/151115727451828646838272)), (45497/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886309179567727/75557863725914323419136), (7099532593247/75557863725914323419136)), (4623/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296426427434585/4722366482869645213696), (2660901488763/2361183241434822606848)), (55509/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809958140701089/295147905179352825856), (457053470345/36893488147419103232)), (9547/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821557696771005/73786976294838206464), (1141767181433/9223372036854775808)), (23887/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820497421741783/9223372036854775808), (1283297339549/1152921504606846976)), (6725/576460752303423488), by norm_num⟩
  | 6 => ⟨((198967783120629/144115188075855872), (10254479606509/1152921504606846976)), (107735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596306755744051/72057594037927936), (4479647276945/72057594037927936)), (23605/36028797018963968), by norm_num⟩
  | 4 => ⟨((372169588491279/9007199254740992), (6706110065439/18014398509481984)), (141935/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485544661994103/9007199254740992), (8359288176765/4503599627370496)), (177953/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110239885607123/2251799813685248), (1040541034141/140737488355328)), (44689/562949953421312), by norm_num⟩
  | 1 => ⟨((551199206735925/562949953421312), (24798635074783/1125899906842624)), (270147/1125899906842624), by norm_num⟩
  | 0 => ⟨((134856799735877/140737488355328), (12225643132237/281474976710656)), (548383/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((134856799735877/140737488355328), (12225643132237/281474976710656)), (2091915134910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063301263604357/2251799813685248), (93718376065589/1125899906842624)), (2197151/2251799813685248), by norm_num⟩
  | 2 => ⟨((937489989714513/1125899906842624), (343492778681093/2251799813685248)), (4392231/2251799813685248), by norm_num⟩
  | 3 => ⟨((188602613207723/281474976710656), (572024279593015/2251799813685248)), (8654451/2251799813685248), by norm_num⟩
  | 4 => ⟨((865675863845067/2251799813685248), (766570977003111/2251799813685248)), (15994827/2251799813685248), by norm_num⟩
  | 5 => ⟨((143674972772699/4503599627370496), (1178793938400213/4503599627370496)), (5797031/562949953421312), by norm_num⟩
  | 6 => ⟨((-303959668858733/4503599627370496), (4700772743401/281474976710656)), (27236501/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-6130311281/67108864)), (1/33554432), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-3109235129/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-17544617491357/18014398509481984), (301316911665783/4503599627370496)), (24583879/4503599627370496), by norm_num⟩
  | 1 => ⟨((104925245/34359738368), (-3604039893/17179869184)), (295/17179869184), by norm_num⟩
  | 2 => ⟨((-82248125/17179869184), (5650223119/17179869184)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((10745355/2147483648), (-5905413969/17179869184)), (487/17179869184), by norm_num⟩
  | 4 => ⟨((-67383997/17179869184), (1157274459/4294967296)), (3/134217728), by norm_num⟩
  | 5 => ⟨((84512853/34359738368), (-1451450949/8589934592)), (483/34359738368), by norm_num⟩
  | 6 => ⟨((-44164927/34359738368), (6068021407/68719476736)), (253/34359738368), by norm_num⟩
  | 7 => ⟨((79130785/137438953472), (-1359017573/34359738368)), (455/137438953472), by norm_num⟩
  | 8 => ⟨((-31014265/137438953472), (4261191739/274877906944)), (359/274877906944), by norm_num⟩
  | 9 => ⟨((86440043/1099511627776), (-5938196467/1099511627776)), (251/549755813888), by norm_num⟩
  | 10 => ⟨((-54206451/2199023255552), (3723836135/2199023255552)), (631/4398046511104), by norm_num⟩
  | 11 => ⟨((7725637/1099511627776), (-4245842423/8796093022208)), (361/8796093022208), by norm_num⟩
  | 12 => ⟨((-64596507/35184372088832), (2218802393/17592186044416)), (379/35184372088832), by norm_num⟩
  | 13 => ⟨((62320607/140737488355328), (-2140628329/70368744177664)), (367/140737488355328), by norm_num⟩
  | 14 => ⟨((-27915129/281474976710656), (1917693641/281474976710656)), (165/281474976710656), by norm_num⟩
  | 15 => ⟨((93362907/4503599627370496), (-3206889237/2251799813685248)), (277/2251799813685248), by norm_num⟩
  | 16 => ⟨((-36592357/9007199254740992), (5027591327/18014398509481984)), (109/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (2065097873561/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888897797798279/316912650057057350374175801344), (610348989877/158456325028528675187087900672)), (46221/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888647131326061/39614081257132168796771975168), (2745926980051/39614081257132168796771975168)), (26003/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236044237892177/309485009821345068724781056), (2916742538343/2475880078570760549798248448)), (27633/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885010142979525/77371252455336267181195264), (2915837443347/154742504910672534362390528)), (13819/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387114078932877/2417851639229258349412352), (1366318146093/4835703278458516698824704)), (6479/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628914427219773/302231454903657293676544), (1195047920635/302231454903657293676544)), (11341/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886232588470297/75557863725914323419136), (3882104869917/75557863725914323419136)), (9217/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((81023130835309/295147905179352825856), (2910003731261/4722366482869645213696)), (6915/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202480077770173/73786976294838206464), (124959295669/18446744073709551616)), (19023/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821465818625447/73786976294838206464), (1248634520677/18446744073709551616)), (47579/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820397758795511/9223372036854775808), (2806794213085/4611686018427387904)), (13389/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591647216636669/1152921504606846976), (2803505748229/576460752303423488)), (53593/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192535521446411/144115188075855872), (612343154965/18014398509481984)), (93871/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488571687954897/36028797018963968), (7333361259497/36028797018963968)), (70487/18014398509481984), by norm_num⟩
  | 3 => ⟨((742714654124893/4503599627370496), (1142616161281/1125899906842624)), (176509/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220302682560487/4503599627370496), (18204748430789/4503599627370496)), (176949/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204664133598401/2251799813685248), (6778767276711/562949953421312)), (533055/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078984276218161/1125899906842624), (13366560522615/562949953421312)), (134373/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078984276218161/1125899906842624), (13366560522615/562949953421312)), (512592316747569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2066777697545081/2251799813685248), (51238333153307/1125899906842624)), (2111429/2251799813685248), by norm_num⟩
  | 2 => ⟨((946147290277739/1125899906842624), (188113070401811/2251799813685248)), (4068059/2251799813685248), by norm_num⟩
  | 3 => ⟨((1574470443951819/2251799813685248), (79040184098433/562949953421312)), (7516851/2251799813685248), by norm_num⟩
  | 4 => ⟨((66030502389203/140737488355328), (110530636863165/562949953421312)), (12622431/2251799813685248), by norm_num⟩
  | 5 => ⟨((408870549840059/2251799813685248), (829731275356761/4503599627370496)), (33601761/4503599627370496), by norm_num⟩
  | 6 => ⟨((-17544617491357/18014398509481984), (301316911665783/4503599627370496)), (24583879/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-3109235129/33554432)), (1/33554432), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-91975095/33554432), (-787859579/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((275038777671985/4503599627370496), (23367589858779/1125899906842624)), (48548097/18014398509481984), by norm_num⟩
  | 1 => ⟨((-3334381259/17179869184), (-70823153/1073741824)), (149/17179869184), by norm_num⟩
  | 2 => ⟨((2649210783/8589934592), (1800638341/17179869184)), (239/17179869184), by norm_num⟩
  | 3 => ⟨((-5612889651/17179869184), (-953754263/8589934592)), (255/17179869184), by norm_num⟩
  | 4 => ⟨((1114879091/4294967296), (757770597/8589934592)), (205/17179869184), by norm_num⟩
  | 5 => ⟨((-5669033225/34359738368), (-1926588599/34359738368)), (263/34359738368), by norm_num⟩
  | 6 => ⟨((6005497585/68719476736), (510233523/17179869184)), (281/68719476736), by norm_num⟩
  | 7 => ⟨((-1363271043/34359738368), (-1853199545/137438953472)), (257/137438953472), by norm_num⟩
  | 8 => ⟨((541568595/34359738368), (736195989/137438953472)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((-6119588081/1099511627776), (-259963387/137438953472)), (293/1099511627776), by norm_num⟩
  | 10 => ⟨((972419017/549755813888), (330471055/549755813888)), (47/549755813888), by norm_num⟩
  | 11 => ⟨((-2247563623/4398046511104), (-1527643349/8796093022208)), (219/8796093022208), by norm_num⟩
  | 12 => ⟨((4761918787/35184372088832), (404577733/8796093022208)), (117/17592186044416), by norm_num⟩
  | 13 => ⟨((-4656502843/140737488355328), (-1582485925/140737488355328)), (231/140737488355328), by norm_num⟩
  | 14 => ⟨((4228176199/562949953421312), (1436921559/562949953421312)), (53/140737488355328), by norm_num⟩
  | 15 => ⟨((-895824771/562949953421312), (-1217763751/2251799813685248)), (91/1125899906842624), by norm_num⟩
  | 16 => ⟨((5693958689/18014398509481984), (1935059377/18014398509481984)), (73/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (213367091029/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777742129217947/633825300114114700748351602688), (252231126773/316912650057057350374175801344)), (23063/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944293581792167/19807040628566084398385987584), (283693189003/19807040628566084398385987584)), (51893/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944145215204741/1237940039285380274899124224), (301339788153/1237940039285380274899124224)), (27569/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769957086289611/154742504910672534362390528), (37655635711/9671406556917033397649408)), (13785/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387099338983777/2417851639229258349412352), (282316688391/4835703278458516698824704)), (3231/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((39305548570353/18889465931478580854784), (15432910631/18889465931478580854784)), (11309/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235768721021889/9444732965739290427392), (802134557361/75557863725914323419136)), (73513/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648154226144317/2361183241434822606848), (300635711173/2361183241434822606848)), (55139/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619756635133595/590295810358705651712), (826213150639/590295810358705651712)), (37911/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821361987212123/73786976294838206464), (1031964512059/73786976294838206464)), (47393/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820282530033971/9223372036854775808), (579929246565/4611686018427387904)), (106647/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795766980228237/576460752303423488), (1158483111189/1152921504606846976)), (53331/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192438635414923/144115188075855872), (506063805147/72057594037927936)), (93347/144115188075855872), by norm_num⟩
  | 4 => ⟨((372107692530687/9007199254740992), (1515106664727/36028797018963968)), (17507/4503599627370496), by norm_num⟩
  | 3 => ⟨((742630423420379/4503599627370496), (1888497308875/9007199254740992)), (43783/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109994341423597/2251799813685248), (3760885602897/4503599627370496)), (350453/4503599627370496), by norm_num⟩
  | 1 => ⟨((551062493222381/562949953421312), (350076689223/140737488355328)), (32885/140737488355328), by norm_num⟩
  | 0 => ⟨((4213603103283/4398046511104), (11043071370185/2251799813685248)), (16473/35184372088832), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((4213603103283/4398046511104), (11043071370185/2251799813685248)), (62839508190858353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2066835983639693/2251799813685248), (10579951730321/1125899906842624)), (1015229/1125899906842624), by norm_num⟩
  | 2 => ⟨((1896866327012867/2251799813685248), (38843639311989/2251799813685248)), (470689/281474976710656), by norm_num⟩
  | 3 => ⟨((1597208158728007/2251799813685248), (16360511041379/562949953421312)), (6473879/2251799813685248), by norm_num⟩
  | 4 => ⟨((1131002509941025/2251799813685248), (23209116154499/562949953421312)), (9560173/2251799813685248), by norm_num⟩
  | 5 => ⟨((564236687741251/2251799813685248), (186514403027979/4503599627370496)), (2597947/562949953421312), by norm_num⟩
  | 6 => ⟨((275038777671985/4503599627370496), (23367589858779/1125899906842624)), (48548097/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-787859579/8388608)), (1/33554432), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-3191918435/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((178939927346187/4503599627370496), (-863720778452289/18014398509481984)), (34030677/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1098604977/8589934592), (331426851/2147483648)), (211/17179869184), by norm_num⟩
  | 2 => ⟨((1768136501/8589934592), (-2133643757/8589934592)), (171/8589934592), by norm_num⟩
  | 3 => ⟨((-3794274559/17179869184), (572327859/2147483648)), (369/17179869184), by norm_num⟩
  | 4 => ⟨((3053324663/17179869184), (-3684504619/17179869184)), (299/17179869184), by norm_num⟩
  | 5 => ⟨((-1965654589/17179869184), (2371992569/17179869184)), (97/8589934592), by norm_num⟩
  | 6 => ⟨((527266503/8589934592), (-1272524923/17179869184)), (105/17179869184), by norm_num⟩
  | 7 => ⟨((-969831657/34359738368), (4681256813/137438953472)), (97/34359738368), by norm_num⟩
  | 8 => ⟨((3121767675/274877906944), (-117721753/8589934592)), (157/137438953472), by norm_num⟩
  | 9 => ⟨((-2233018333/549755813888), (168414091/34359738368)), (227/549755813888), by norm_num⟩
  | 10 => ⟨((2875123491/2199023255552), (-3469465895/2199023255552)), (147/1099511627776), by norm_num⟩
  | 11 => ⟨((-3365332909/8796093022208), (4061010871/8796093022208)), (173/4398046511104), by norm_num⟩
  | 12 => ⟨((3610862915/35184372088832), (-1089324143/8796093022208)), (187/17592186044416), by norm_num⟩
  | 13 => ⟨((-3576282875/140737488355328), (539446023/17592186044416)), (93/35184372088832), by norm_num⟩
  | 14 => ⟨((205564473/35184372088832), (-496117075/70368744177664)), (345/562949953421312), by norm_num⟩
  | 15 => ⟨((-2823195787/2251799813685248), (3406803753/2251799813685248)), (149/1125899906842624), by norm_num⟩
  | 16 => ⟨((2271879167/9007199254740992), (-342689945/1125899906842624)), (241/9007199254740992), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-1144738541017/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222210883423773/79228162514264337593543950336), (-676584880625/316912650057057350374175801344)), (46167/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944262593749873/19807040628566084398385987584), (-1521952428549/39614081257132168796771975168)), (51943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472056134270583/618970019642690137449562112), (-404154182127/618970019642690137449562112)), (27597/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769891143835325/154742504910672534362390528), (-808051026843/77371252455336267181195264)), (1725/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774167741370215/4835703278458516698824704), (-1514549057579/9671406556917033397649408)), (12939/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628861681561393/302231454903657293676544), (-662342030013/302231454903657293676544)), (45293/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886061610064045/75557863725914323419136), (-1075793849281/37778931862957161709568)), (73611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648121124248785/2361183241434822606848), (-806397699027/2361183241434822606848)), (27609/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619665466699067/590295810358705651712), (-2216139690379/590295810358705651712)), (18985/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227655977469637/9223372036854775808), (-2767995395425/73786976294838206464)), (94949/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820153807826125/9223372036854775808), (-388875155709/1152921504606846976)), (106851/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795702442247497/576460752303423488), (-3107263548447/1152921504606846976)), (26723/288230376151711744), by norm_num⟩
  | 5 => ⟨((298081324344727/36028797018963968), (-2714656560275/144115188075855872)), (93577/144115188075855872), by norm_num⟩
  | 4 => ⟨((93016248339279/2251799813685248), (-4063601391591/36028797018963968)), (70229/18014398509481984), by norm_num⟩
  | 3 => ⟨((92815373559497/562949953421312), (-316553974121/562949953421312)), (175735/9007199254740992), by norm_num⟩
  | 2 => ⟨((277444356535855/562949953421312), (-5042971972043/2251799813685248)), (351963/4503599627370496), by norm_num⟩
  | 1 => ⟨((275448638630451/281474976710656), (-15019915838579/2251799813685248)), (132295/562949953421312), by norm_num⟩
  | 0 => ⟨((1078001619330853/1125899906842624), (-14803284380837/1125899906842624)), (1063343/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1078001619330853/1125899906842624), (-14803284380837/1125899906842624)), (4056331643111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2063892797202061/2251799813685248), (-14173519721401/562949953421312)), (2064175/2251799813685248), by norm_num⟩
  | 2 => ⟨((945119373821215/1125899906842624), (-103926201916241/2251799813685248)), (3887791/2251799813685248), by norm_num⟩
  | 3 => ⟨((49435481647765/70368744177664), (-87239253047051/1125899906842624)), (1721489/562949953421312), by norm_num⟩
  | 4 => ⟨((548911338816981/1125899906842624), (-245149436351097/2251799813685248)), (5371077/1125899906842624), by norm_num⟩
  | 5 => ⟨((508533830771603/2251799813685248), (-239036000447095/2251799813685248)), (25626459/4503599627370496), by norm_num⟩
  | 6 => ⟨((178939927346187/4503599627370496), (-863720778452289/18014398509481984)), (34030677/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-3191918435/33554432)), (1/33554432), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-188583173/67108864), (-6461621367/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-488307848037419/18014398509481984), (-484139463481039/9007199254740992)), (24380723/4503599627370496), by norm_num⟩
  | 1 => ⟨((1517252073/17179869184), (3008600445/17179869184)), (305/17179869184), by norm_num⟩
  | 2 => ⟨((-2471676863/17179869184), (-4901155347/17179869184)), (499/17179869184), by norm_num⟩
  | 3 => ⟨((1342160305/8589934592), (5322812423/17179869184)), (17/536870912), by norm_num⟩
  | 4 => ⟨((-1093221961/8589934592), (-2167779591/8589934592)), (445/17179869184), by norm_num⟩
  | 5 => ⟨((2849458149/34359738368), (353141759/2147483648)), (291/17179869184), by norm_num⟩
  | 6 => ⟨((-773650811/17179869184), (-3068186513/34359738368)), (159/17179869184), by norm_num⟩
  | 7 => ⟨((1440359445/68719476736), (2856127959/68719476736)), (297/68719476736), by norm_num⟩
  | 8 => ⟨((-2346415061/274877906944), (-1163192577/68719476736)), (243/137438953472), by norm_num⟩
  | 9 => ⟨((849427421/274877906944), (1684352759/274877906944)), (177/274877906944), by norm_num⟩
  | 10 => ⟨((-138375827/137438953472), (-2195113557/1099511627776)), (463/2199023255552), by norm_num⟩
  | 11 => ⟨((655769895/2199023255552), (5201375913/8796093022208)), (551/8796093022208), by norm_num⟩
  | 12 => ⟨((-2848748833/35184372088832), (-2824430809/17592186044416)), (601/35184372088832), by norm_num⟩
  | 13 => ⟨((2855845757/140737488355328), (2831467151/70368744177664)), (151/35184372088832), by norm_num⟩
  | 14 => ⟨((-2658463193/562949953421312), (-5271539041/562949953421312)), (565/562949953421312), by norm_num⟩
  | 15 => ⟨((577435315/562949953421312), (4580048827/2251799813685248)), (493/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1881340001/9007199254740992), (-3730560307/9007199254740992)), (403/9007199254740992), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197539410918425/1267650600228229401496703205376), (-1327284388925/5070602400912917605986812821504)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777630680631135/633825300114114700748351602688), (-1568865421177/316912650057057350374175801344)), (46255/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888461533158457/39614081257132168796771975168), (-3529086058979/39614081257132168796771975168)), (52047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118009787947049/154742504910672534362390528), (-1874289340017/1237940039285380274899124224)), (55311/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442455719999005/38685626227668133590597632), (-3747369499143/154742504910672534362390528)), (55325/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548271130927689/9671406556917033397649408), (-1755937303585/4835703278458516698824704)), (6485/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257666701178769/604462909807314587353088), (-3071606496317/604462909807314587353088)), (45409/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942984435603829/37778931862957161709568), (-4988954550167/75557863725914323419136)), (73815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81010757175739/295147905179352825856), (-3739611747109/4722366482869645213696)), (55385/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619568092535829/590295810358705651712), (-2569274463133/295147905179352825856)), (38095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455281173501147/18446744073709551616), (-6418063892263/73786976294838206464)), (95293/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113750834955979/576460752303423488), (-901660570905/1152921504606846976)), (6705/576460752303423488), by norm_num⟩
  | 6 => ⟨((795631013446659/576460752303423488), (-112570259805/18014398509481984)), (107375/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149024699376333/18014398509481984), (-6294060069793/144115188075855872)), (94061/144115188075855872), by norm_num⟩
  | 4 => ⟨((93003939780849/2251799813685248), (-9421371000685/36028797018963968)), (141305/36028797018963968), by norm_num⟩
  | 3 => ⟨((742395215490397/4503599627370496), (-5871136207769/4503599627370496)), (177007/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219015819790467/4503599627370496), (-23381488831411/4503599627370496)), (44393/562949953421312), by norm_num⟩
  | 1 => ⟨((34417364838229/35184372088832), (-34815529558007/2251799813685248)), (535551/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076987349842617/1125899906842624), (-17152462131407/562949953421312)), (1082499/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076987349842617/1125899906842624), (-17152462131407/562949953421312)), (4129405983931731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257288617942463/281474976710656), (-131258451106787/2251799813685248)), (1068455/1125899906842624), by norm_num⟩
  | 2 => ⟨((1873793087833677/2251799813685248), (-239959557849073/2251799813685248)), (2077853/1125899906842624), by norm_num⟩
  | 3 => ⟨((1533670944291529/2251799813685248), (-99838928426181/562949953421312)), (7801879/2251799813685248), by norm_num⟩
  | 4 => ⟨((121717168527239/281474976710656), (-543991744579967/2251799813685248)), (13394833/2251799813685248), by norm_num⟩
  | 5 => ⟨((289651593884741/2251799813685248), (-940945239626481/4503599627370496)), (9028213/1125899906842624), by norm_num⟩
  | 6 => ⟨((-488307848037419/18014398509481984), (-484139463481039/9007199254740992)), (24380723/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-188583173/67108864), (-6461621367/67108864)), (1/33554432), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-51066171/524288)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1049637174697929/18014398509481984), (24392941196519/36028797018963968)), (171607371/36028797018963968), by norm_num⟩
  | 1 => ⟨((6598344605/34359738368), (-38335397/17179869184)), (541/34359738368), by norm_num⟩
  | 2 => ⟨((-5436766851/17179869184), (63173607/17179869184)), (7/268435456), by norm_num⟩
  | 3 => ⟨((5972898873/17179869184), (-69403301/17179869184)), (247/8589934592), by norm_num⟩
  | 4 => ⟨((-4921425075/17179869184), (28592745/8589934592)), (409/17179869184), by norm_num⟩
  | 5 => ⟨((3244042839/17179869184), (-37694809/17179869184)), (541/34359738368), by norm_num⟩
  | 6 => ⟨((-222746583/2147483648), (82823961/68719476736)), (597/68719476736), by norm_num⟩
  | 7 => ⟨((6712104229/137438953472), (-77992647/137438953472)), (141/34359738368), by norm_num⟩
  | 8 => ⟨((-5530500141/274877906944), (8032845/34359738368)), (467/274877906944), by norm_num⟩
  | 9 => ⟨((8101167223/1099511627776), (-11766643/137438953472)), (343/549755813888), by norm_num⟩
  | 10 => ⟨((-2670012559/1099511627776), (62049497/2199023255552)), (227/1099511627776), by norm_num⟩
  | 11 => ⟨((3199973027/4398046511104), (-37182731/4398046511104)), (273/4398046511104), by norm_num⟩
  | 12 => ⟨((-3515529691/17592186044416), (40849405/17592186044416)), (301/17592186044416), by norm_num⟩
  | 13 => ⟨((3565111495/70368744177664), (-41425531/70368744177664)), (613/140737488355328), by norm_num⟩
  | 14 => ⟨((-209821891/17592186044416), (78018167/562949953421312)), (579/562949953421312), by norm_num⟩
  | 15 => ⟨((2950565221/1125899906842624), (-34284687/1125899906842624)), (511/2251799813685248), by norm_num⟩
  | 16 => ⟨((-4862290815/9007199254740992), (882787/140737488355328)), (423/9007199254740992), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1019284978653/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777573383748283/633825300114114700748351602688), (4818967086739/633825300114114700748351602688)), (23169/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944198349705407/19807040628566084398385987584), (5419979354995/39614081257132168796771975168)), (26073/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944043606501899/1237940039285380274899124224), (1439263775597/618970019642690137449562112)), (27711/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769752914705655/154742504910672534362390528), (5755173387787/154742504910672534362390528)), (55443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387051233043715/2417851639229258349412352), (1348369063307/2417851639229258349412352)), (25999/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157201021448685/75557863725914323419136), (2358646755983/302231454903657293676544)), (2845/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((58933519571089/2361183241434822606848), (7661856564139/75557863725914323419136)), (74009/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296098939855691/4722366482869645213696), (2871558227439/2361183241434822606848)), (27771/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619465868614651/590295810358705651712), (986433002789/73786976294838206464)), (38213/295147905179352825856), by norm_num⟩
  | 8 => ⟨((222289368387/9007199254740992), (9856352478453/73786976294838206464)), (95617/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909931796563105/4611686018427387904), (11077434080999/9223372036854775808)), (53843/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795554070246201/576460752303423488), (11063741022951/1152921504606846976)), (13479/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192058323366059/144115188075855872), (9665382479359/144115188075855872)), (94517/144115188075855872), by norm_num⟩
  | 4 => ⟨((371961230604363/9007199254740992), (14467326341845/36028797018963968)), (142105/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484501756472407/9007199254740992), (18030427587761/9007199254740992)), (5569/281474976710656), by norm_num⟩
  | 2 => ⟨((1109195346389547/2251799813685248), (2243748417413/281474976710656)), (44769/562949953421312), by norm_num⟩
  | 1 => ⟨((1100827661177025/1125899906842624), (26724424332067/1125899906842624)), (270791/1125899906842624), by norm_num⟩
  | 0 => ⟨((1075697958059829/1125899906842624), (26324944897417/562949953421312)), (550329/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1075697958059829/1125899906842624), (26324944897417/562949953421312)), (2099338535789107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((512636193973871/562949953421312), (201209285479741/2251799813685248)), (2206103/2251799813685248), by norm_num⟩
  | 2 => ⟨((1849297915418987/2251799813685248), (366452334434571/2251799813685248)), (4412117/2251799813685248), by norm_num⟩
  | 3 => ⟨((1459106376415981/2251799813685248), (37618771329699/140737488355328)), (4341483/1125899906842624), by norm_num⟩
  | 4 => ⟨((392287845956261/1125899906842624), (780030818533795/2251799813685248)), (3973633/562949953421312), by norm_num⟩
  | 5 => ⟨((1578945524885/1125899906842624), (2174236681057959/9007199254740992)), (44175665/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1049637174697929/18014398509481984), (24392941196519/36028797018963968)), (171607371/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-51066171/524288)), (1/33554432), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile049Terms3

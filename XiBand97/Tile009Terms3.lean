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
namespace Reinmann.XiBand97.Tile009Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (12067/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (12067/640))
  have he : value ((69/80), (12067/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-1955573755/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-201000452388085/18014398509481984), (-1236273795623171/18014398509481984)), (106175513/9007199254740992), by norm_num⟩
  | 1 => ⟨((296259371/8589934592), (911086747/4294967296)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-228937573/4294967296), (-1408103907/4294967296)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((58971313/1073741824), (725418159/2147483648)), (1/16777216), by norm_num⟩
  | 4 => ⟨((-11392677/268435456), (-1121149163/4294967296)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((225377589/8589934592), (173275983/1073741824)), (31/1073741824), by norm_num⟩
  | 6 => ⟨((-14513577/1073741824), (-714137893/8589934592)), (129/8589934592), by norm_num⟩
  | 7 => ⟨((102541903/17179869184), (1261388883/34359738368)), (115/17179869184), by norm_num⟩
  | 8 => ⟨((-9905043/4294967296), (-974751647/68719476736)), (179/68719476736), by norm_num⟩
  | 9 => ⟨((108860119/137438953472), (1339110543/274877906944)), (31/34359738368), by norm_num⟩
  | 10 => ⟨((-269192999/1099511627776), (-1655699015/1099511627776)), (309/1099511627776), by norm_num⟩
  | 11 => ⟨((151288543/2199023255552), (465257813/1099511627776)), (11/137438953472), by norm_num⟩
  | 12 => ⟨((-77939885/4398046511104), (-958754435/8796093022208)), (183/8796093022208), by norm_num⟩
  | 13 => ⟨((18531961/4398046511104), (455930871/17592186044416)), (351/70368744177664), by norm_num⟩
  | 14 => ⟨((-65466375/70368744177664), (-1610630489/281474976710656)), (39/35184372088832), by norm_num⟩
  | 15 => ⟨((215849967/1125899906842624), (663803629/562949953421312)), (259/1125899906842624), by norm_num⟩
  | 16 => ⟨((-166800353/4503599627370496), (-1025922599/4503599627370496)), (201/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-1128043280119/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777854020685095/633825300114114700748351602688), (-83354849087/19807040628566084398385987584)), (92463/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472178202503569/9903520314283042199192993792), (-3000079764869/39614081257132168796771975168)), (52019/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472105905512429/618970019642690137449562112), (-3186717692487/2475880078570760549798248448)), (3455/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770089932154121/154742504910672534362390528), (-1592871323491/77371252455336267181195264)), (55291/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548521531827837/9671406556917033397649408), (-373199763651/1208925819614629174706176)), (51847/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257885841369123/604462909807314587353088), (-2611363132131/604462909807314587353088)), (22689/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886325047686487/75557863725914323419136), (-1060381233289/18889465931478580854784)), (73761/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296439311421387/4722366482869645213696), (-3179446931137/4722366482869645213696)), (13835/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619935591886973/590295810358705651712), (-4368983908351/590295810358705651712)), (152247/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910792111762267/36893488147419103232), (-5457099298607/73786976294838206464)), (190403/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910265271234395/4611686018427387904), (-1533390444029/2305843009213693952)), (53583/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591779473973157/1152921504606846976), (-6126475035713/1152921504606846976)), (107247/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192650655806353/144115188075855872), (-669087823917/18014398509481984)), (23483/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488743211168639/36028797018963968), (-8013151527931/36028797018963968)), (282161/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485641657589295/9007199254740992), (-2497165924701/2251799813685248)), (353339/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110360623350371/2251799813685248), (-9947106799477/2251799813685248)), (708599/4503599627370496), by norm_num⟩
  | 1 => ⟨((551319186585045/562949953421312), (-29634281069533/2251799813685248)), (1067715/2251799813685248), by norm_num⟩
  | 0 => ⟨((134945841156831/140737488355328), (-58444863812867/2251799813685248)), (538699/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((134945841156831/140737488355328), (-58444863812867/2251799813685248)), (2054973604442405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2068763600226213/2251799813685248), (-112079466540021/2251799813685248)), (2122049/1125899906842624), by norm_num⟩
  | 2 => ⟨((1895026814047641/2251799813685248), (-51484576759801/562949953421312)), (2055181/562949953421312), by norm_num⟩
  | 3 => ⟨((1575946502031913/2251799813685248), (-173309639474647/1125899906842624)), (7670067/1125899906842624), by norm_num⟩
  | 4 => ⟨((1049588173141955/2251799813685248), (-60646314658737/281474976710656)), (26194529/2251799813685248), by norm_num⟩
  | 5 => ⟨((769380028461633/4503599627370496), (-904572837760837/4503599627370496)), (35706799/2251799813685248), by norm_num⟩
  | 6 => ⟨((-201000452388085/18014398509481984), (-1236273795623171/18014398509481984)), (106175513/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-1955573755/33554432)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-1983696533/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-126731091692775/2251799813685248), (-325994117734771/9007199254740992)), (6877473/562949953421312), by norm_num⟩
  | 1 => ⟨((189478209/1073741824), (487400375/4294967296)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-1188215657/4294967296), (-47757533/268435456)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((620940553/2147483648), (99828979/536870912)), (277/4294967296), by norm_num⟩
  | 4 => ⟨((-243369439/1073741824), (-156506593/1073741824)), (219/4294967296), by norm_num⟩
  | 5 => ⟨((1220933549/8589934592), (785160827/8589934592)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((-1276076693/17179869184), (-410311205/8589934592)), (73/4294967296), by norm_num⟩
  | 7 => ⟨((1143180311/34359738368), (735159091/34359738368)), (33/4294967296), by norm_num⟩
  | 8 => ⟨((-896108813/68719476736), (-576271769/68719476736)), (209/68719476736), by norm_num⟩
  | 9 => ⟨((1248775111/274877906944), (200766311/68719476736)), (293/274877906944), by norm_num⟩
  | 10 => ⟨((-783105427/549755813888), (-503601285/549755813888)), (93/274877906944), by norm_num⟩
  | 11 => ⟨((446440461/1099511627776), (574195969/2199023255552)), (107/1099511627776), by norm_num⟩
  | 12 => ⟨((-933207655/8796093022208), (-150032345/2199023255552)), (113/4398046511104), by norm_num⟩
  | 13 => ⟨((450164185/17592186044416), (144746323/8796093022208)), (55/8796093022208), by norm_num⟩
  | 14 => ⟨((-806564113/140737488355328), (-518687153/140737488355328)), (199/140737488355328), by norm_num⟩
  | 15 => ⟨((84299237/70368744177664), (216845409/281474976710656)), (21/70368744177664), by norm_num⟩
  | 16 => ⟨((-132159885/562949953421312), (-339958763/2251799813685248)), (265/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-3347836772833/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888895195086137/316912650057057350374175801344), (-3957873026227/633825300114114700748351602688)), (46295/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118040061945437/2475880078570760549798248448), (-4451550920061/39614081257132168796771975168)), (104189/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888346997818533/2475880078570760549798248448), (-2364233264129/1237940039285380274899124224)), (55365/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442503238024369/38685626227668133590597632), (-1181749329449/38685626227668133590597632)), (110763/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548448985287955/9671406556917033397649408), (-138437481357/302231454903657293676544)), (103875/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78613874111173/37778931862957161709568), (-1937344703155/302231454903657293676544)), (45463/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471555143892615/18889465931478580854784), (-3146723117599/37778931862957161709568)), (147819/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296360339683015/4722366482869645213696), (-2358763608427/2361183241434822606848)), (110921/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809913001764731/295147905179352825856), (-6482446084177/590295810358705651712)), (152609/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910722868657563/36893488147419103232), (-8096830403629/73786976294838206464)), (190901/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820372686095533/9223372036854775808), (-9100377581045/9223372036854775808)), (107477/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591619049598337/1152921504606846976), (-4544845234773/576460752303423488)), (107597/576460752303423488), by norm_num⟩
  | 5 => ⟨((149063425504225/18014398509481984), (-7941468075607/144115188075855872)), (188565/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488522593973879/36028797018963968), (-371506553869/1125899906842624)), (283387/36028797018963968), by norm_num⟩
  | 3 => ⟨((92834743115231/562949953421312), (-14818342460297/9007199254740992)), (355181/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110059956825717/2251799813685248), (-29511193687173/4503599627370496)), (356605/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204300919618055/2251799813685248), (-43953999468957/2251799813685248)), (269239/562949953421312), by norm_num⟩
  | 0 => ⟨((2156890477415011/2251799813685248), (-43331226568831/1125899906842624)), (2182607/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156890477415011/2251799813685248), (-43331226568831/1125899906842624)), (8325984963423918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257830765114637/281474976710656), (-41504892838617/562949953421312)), (1087307/562949953421312), by norm_num⟩
  | 2 => ⟨((117321333816301/140737488355328), (-304147484842521/2251799813685248)), (2152273/562949953421312), by norm_num⟩
  | 3 => ⟨((190467304249851/281474976710656), (-253542883389441/1125899906842624)), (16679029/2251799813685248), by norm_num⟩
  | 4 => ⟨((458442803802453/1125899906842624), (-343132665470031/1125899906842624)), (3760567/281474976710656), by norm_num⟩
  | 5 => ⟨((164188268750973/2251799813685248), (-1117731338484093/4503599627370496)), (85673785/4503599627370496), by norm_num⟩
  | 6 => ⟨((-126731091692775/2251799813685248), (-325994117734771/9007199254740992)), (6877473/562949953421312), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1983696533/33554432)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-91975095/33554432), (-2010622227/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1131099466568827/18014398509481984), (265974799158325/18014398509481984)), (100926259/9007199254740992), by norm_num⟩
  | 1 => ⟨((107130259/536870912), (-50382747/1073741824)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-170232865/536870912), (80059541/1073741824)), (247/4294967296), by norm_num⟩
  | 3 => ⟨((1442691223/4294967296), (-84811177/1073741824)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-143279699/536870912), (134767243/2147483648)), (211/4294967296), by norm_num⟩
  | 5 => ⟨((364280477/2147483648), (-171319021/4294967296)), (135/4294967296), by norm_num⟩
  | 6 => ⟨((-1543603953/17179869184), (362974047/17179869184)), (9/536870912), by norm_num⟩
  | 7 => ⟨((700808065/17179869184), (-329586017/34359738368)), (263/34359738368), by norm_num⟩
  | 8 => ⟨((-1113602877/68719476736), (130930263/34359738368)), (211/68719476736), by norm_num⟩
  | 9 => ⟨((1572928839/274877906944), (-184934855/137438953472)), (75/68719476736), by norm_num⟩
  | 10 => ⟨((-124971313/68719476736), (117546585/274877906944)), (3/8589934592), by norm_num⟩
  | 11 => ⟨((4513245/8589934592), (-135843409/1099511627776)), (7/68719476736), by norm_num⟩
  | 12 => ⟨((-611982317/4398046511104), (287811777/8796093022208)), (239/8796093022208), by norm_num⟩
  | 13 => ⟨((598434691/17592186044416), (-140720203/17592186044416)), (59/8796093022208), by norm_num⟩
  | 14 => ⟨((-1086775807/140737488355328), (255552217/140737488355328)), (27/17592186044416), by norm_num⟩
  | 15 => ⟨((921021871/562949953421312), (-108287827/281474976710656)), (185/562949953421312), by norm_num⟩
  | 16 => ⟨((-731764271/2251799813685248), (344144543/4503599627370496)), (37/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (3791435219681/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777731488876019/633825300114114700748351602688), (4482031286711/633825300114114700748351602688)), (46321/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888574613625375/39614081257132168796771975168), (5041067439371/39614081257132168796771975168)), (104251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944138158337849/1237940039285380274899124224), (5354634055165/2475880078570760549798248448)), (110799/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884971048371909/77371252455336267181195264), (1338236701315/38685626227668133590597632)), (110837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387095593367249/2417851639229258349412352), (2508297700251/4835703278458516698824704)), (103949/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628881757854031/302231454903657293676544), (1096932319479/151115727451828646838272)), (90995/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886125215754259/75557863725914323419136), (3563350887091/37778931862957161709568)), (147939/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296288517528975/4722366482869645213696), (1335522236641/1180591620717411303424)), (111019/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50616461175681/18446744073709551616), (7340601172479/590295810358705651712)), (38189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227665118202851/9223372036854775808), (573037405169/4611686018427387904)), (191103/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820231287977977/9223372036854775808), (10304843972441/9223372036854775808)), (26901/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397869098865321/288230376151711744), (10292566369793/1152921504606846976)), (215479/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192381173186825/144115188075855872), (4496097857301/72057594037927936)), (94425/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488330442091899/36028797018963968), (13460724972509/36028797018963968)), (141943/18014398509481984), by norm_num⟩
  | 3 => ⟨((742555407818987/4503599627370496), (4194432801621/2251799813685248)), (88983/2251799813685248), by norm_num⟩
  | 2 => ⟨((277451901722299/562949953421312), (8352804414495/1125899906842624)), (44693/281474976710656), by norm_num⟩
  | 1 => ⟨((550876961383971/562949953421312), (1554912376629/70368744177664)), (540361/1125899906842624), by norm_num⟩
  | 0 => ⟨((538790587189409/562949953421312), (12260220370335/281474976710656)), (548489/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((538790587189409/562949953421312), (12260220370335/281474976710656)), (2092319490672874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2058399991467691/2251799813685248), (187745039636535/2251799813685248)), (4390727/2251799813685248), by norm_num⟩
  | 2 => ⟨((932978655435971/1125899906842624), (21452527975471/140737488355328)), (8759403/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493908410809043/2251799813685248), (71106678611903/281474976710656)), (17187367/2251799813685248), by norm_num⟩
  | 4 => ⟨((3310144027491/8796093022208), (754787274409931/2251799813685248)), (15744493/1125899906842624), by norm_num⟩
  | 5 => ⟨((131785806652567/4503599627370496), (284041401347877/1125899906842624)), (89619255/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1131099466568827/18014398509481984), (265974799158325/18014398509481984)), (100926259/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-2010622227/33554432)), (1/16777216), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-2036448603/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-605482955269287/18014398509481984), (944307119314021/18014398509481984)), (101997569/9007199254740992), by norm_num⟩
  | 1 => ⟨((232335859/2147483648), (-724698867/4294967296)), (159/4294967296), by norm_num⟩
  | 2 => ⟨((-93482535/536870912), (145794729/536870912)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((802423125/4294967296), (-312863419/1073741824)), (279/4294967296), by norm_num⟩
  | 4 => ⟨((-161431275/1073741824), (62941781/268435456)), (113/2147483648), by norm_num⟩
  | 5 => ⟨((415701783/4294967296), (-1296651375/8589934592)), (293/8589934592), by norm_num⟩
  | 6 => ⟨((-446030807/8589934592), (695626627/8589934592)), (159/8589934592), by norm_num⟩
  | 7 => ⟨((820410161/34359738368), (-1279506133/34359738368)), (295/34359738368), by norm_num⟩
  | 8 => ⟨((-660199609/68719476736), (128705355/8589934592)), (239/68719476736), by norm_num⟩
  | 9 => ⟨((472244569/137438953472), (-736509433/137438953472)), (173/137438953472), by norm_num⟩
  | 10 => ⟨((-608038651/549755813888), (237073241/137438953472)), (225/549755813888), by norm_num⟩
  | 11 => ⟨((711709423/2199023255552), (-1109977199/2199023255552)), (265/2199023255552), by norm_num⟩
  | 12 => ⟨((-11931793/137438953472), (1190959591/8796093022208)), (143/4398046511104), by norm_num⟩
  | 13 => ⟨((756321675/35184372088832), (-1179554165/35184372088832)), (285/35184372088832), by norm_num⟩
  | 14 => ⟨((-86946627/17592186044416), (135601371/17592186044416)), (33/17592186044416), by norm_num⟩
  | 15 => ⟨((149264211/140737488355328), (-931165813/562949953421312)), (229/562949953421312), by norm_num⟩
  | 16 => ⟨((-30028935/140737488355328), (749326781/2251799813685248)), (93/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (87151040315/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777682218983819/633825300114114700748351602688), (3296617299137/633825300114114700748351602688)), (92525/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888519469452351/39614081257132168796771975168), (926949657593/9903520314283042199192993792)), (6507/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((118013631659665/154742504910672534362390528), (1969209882497/1237940039285380274899124224)), (110643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884942157151739/77371252455336267181195264), (1968582209927/77371252455336267181195264)), (55335/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548328656473317/9671406556917033397649408), (3689758294815/9671406556917033397649408)), (51891/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628858483482205/302231454903657293676544), (806801417821/151115727451828646838272)), (90839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886050423717057/75557863725914323419136), (5241711235005/75557863725914323419136)), (147667/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296233166083525/4722366482869645213696), (3929098780613/4722366482869645213696)), (55399/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101228240902015/36893488147419103232), (5398962812651/590295810358705651712)), (19053/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821229121325291/73786976294838206464), (3371692532801/36893488147419103232)), (95323/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820130462411789/9223372036854775808), (1894750280351/2305843009213693952)), (53659/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198922332355581/144115188075855872), (7569875957183/1152921504606846976)), (53709/288230376151711744), by norm_num⟩
  | 5 => ⟨((596149559544177/72057594037927936), (6613387583231/144115188075855872)), (188207/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488214267797733/36028797018963968), (618725213641/2251799813685248)), (35345/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484977630807523/9007199254740992), (12338734837033/9007199254740992)), (354239/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109692363971545/2251799813685248), (6142607247013/1125899906842624)), (177713/1125899906842624), by norm_num⟩
  | 1 => ⟨((137703192204515/140737488355328), (36588976948513/2251799813685248)), (134029/281474976710656), by norm_num⟩
  | 0 => ⟨((1077500077570527/1125899906842624), (36058443448235/1125899906842624)), (542099/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077500077570527/1125899906842624), (36058443448235/1125899906842624)), (2067943575145530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1030026025202153/1125899906842624), (138033497920793/2251799813685248)), (536157/281474976710656), by norm_num⟩
  | 2 => ⟨((938085432406307/1125899906842624), (31569878979477/281474976710656)), (4186941/1125899906842624), by norm_num⟩
  | 3 => ⟨((1534874915791681/2251799813685248), (52607240472251/281474976710656)), (989527/140737488355328), by norm_num⟩
  | 4 => ⟨((483772936181689/1125899906842624), (286865762397351/1125899906842624)), (6875391/562949953421312), by norm_num⟩
  | 5 => ⟨((269552004088139/2251799813685248), (493038115809573/2251799813685248)), (18823849/1125899906842624), by norm_num⟩
  | 6 => ⟨((-605482955269287/18014398509481984), (944307119314021/18014398509481984)), (101997569/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-2036448603/33554432)), (1/16777216), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47145793/16777216), (-1030630957/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((91378780978019/9007199254740992), (267232149012035/4503599627370496)), (83482701/4503599627370496), by norm_num⟩
  | 1 => ⟨((-141964383/4294967296), (-830333843/4294967296)), (521/8589934592), by norm_num⟩
  | 2 => ⟨((14454177/268435456), (676326955/2147483648)), (213/2147483648), by norm_num⟩
  | 3 => ⟨((-125581611/2147483648), (-734512837/2147483648)), (465/4294967296), by norm_num⟩
  | 4 => ⟨((102289253/2147483648), (598278433/2147483648)), (95/1073741824), by norm_num⟩
  | 5 => ⟨((-266614609/8589934592), (-1559399113/8589934592)), (497/8589934592), by norm_num⟩
  | 6 => ⟨((289552045/17179869184), (1693557617/17179869184)), (271/8589934592), by norm_num⟩
  | 7 => ⟨((-33692447/4294967296), (-1576506917/34359738368)), (253/17179869184), by norm_num⟩
  | 8 => ⟨((109773245/34359738368), (321025733/17179869184)), (207/34359738368), by norm_num⟩
  | 9 => ⟨((-158956369/137438953472), (-929718071/137438953472)), (151/68719476736), by norm_num⟩
  | 10 => ⟨((103579039/274877906944), (302911123/137438953472)), (99/137438953472), by norm_num⟩
  | 11 => ⟨((-245433097/2199023255552), (-1435510809/2199023255552)), (471/2199023255552), by norm_num⟩
  | 12 => ⟨((266548241/8796093022208), (1559010933/8796093022208)), (257/4398046511104), by norm_num⟩
  | 13 => ⟨((-267212277/35184372088832), (-1562894807/35184372088832)), (259/17592186044416), by norm_num⟩
  | 14 => ⟨((248743827/140737488355328), (1454874903/140737488355328)), (121/35184372088832), by norm_num⟩
  | 15 => ⟨((-6753595/17592186044416), (-1264032769/562949953421312)), (423/562949953421312), by norm_num⟩
  | 16 => ⟨((44007729/562949953421312), (1029585197/2251799813685248)), (173/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (228194925909/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777633465075491/633825300114114700748351602688), (67432257085/19807040628566084398385987584)), (92413/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944232408380637/19807040628566084398385987584), (2426972856757/39614081257132168796771975168)), (51989/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888160299881191/2475880078570760549798248448), (2577919635107/2475880078570760549798248448)), (220985/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769826801830227/154742504910672534362390528), (2577088633825/154742504910672534362390528)), (221021/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774137525431179/4835703278458516698824704), (603784500847/2417851639229258349412352)), (207245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314417593525121/151115727451828646838272), (132022722111/37778931862957161709568)), (181377/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942987647394629/37778931862957161709568), (3430937483241/75557863725914323419136)), (294809/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324044332548799/1180591620717411303424), (2571757313633/4722366482869645213696)), (221169/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619575909007087/590295810358705651712), (3533818441125/590295810358705651712)), (304209/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910567715465637/36893488147419103232), (4413753978229/73786976294838206464)), (380413/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910013382194519/4611686018427387904), (620079865463/1152921504606846976)), (214087/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795638542780549/576460752303423488), (2477301338025/576460752303423488)), (107109/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192212626140651/144115188075855872), (4328495668695/144115188075855872)), (375177/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488089279119763/36028797018963968), (809900361495/4503599627370496)), (140839/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484829671486435/9007199254740992), (2018839654151/2251799813685248)), (705231/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219113490236455/4503599627370496), (16079986113781/4503599627370496)), (1413581/4503599627370496), by norm_num⟩
  | 1 => ⟨((550726350711551/562949953421312), (23943863101161/2251799813685248)), (1064099/1125899906842624), by norm_num⟩
  | 0 => ⟨((269318806741541/281474976710656), (23593758822419/1125899906842624)), (2143939/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((269318806741541/281474976710656), (23593758822419/1125899906842624)), (8178478245261764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060512203846851/2251799813685248), (90299223708735/2251799813685248)), (8385101/2251799813685248), by norm_num⟩
  | 2 => ⟨((235231644851697/281474976710656), (41314208154507/562949953421312)), (1001131/140737488355328), by norm_num⟩
  | 3 => ⟨((1560556790729391/2251799813685248), (276213800700875/2251799813685248)), (14562043/1125899906842624), by norm_num⟩
  | 4 => ⟨((1047625734337917/2251799813685248), (95711732401177/562949953421312)), (47512453/2251799813685248), by norm_num⟩
  | 5 => ⟨((844611409913039/4503599627370496), (356230863266437/2251799813685248)), (120730567/4503599627370496), by norm_num⟩
  | 6 => ⟨((91378780978019/9007199254740992), (267232149012035/4503599627370496)), (83482701/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1030630957/16777216)), (1/8388608), by norm_num⟩, -10, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-1042569323/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((809664033214025/18014398509481984), (668080164143877/18014398509481984)), (113966295/18014398509481984), by norm_num⟩
  | 1 => ⟨((-636224883/4294967296), (-32810617/268435456)), (91/4294967296), by norm_num⟩
  | 2 => ⟨((131055839/536870912), (865107529/4294967296)), (19/536870912), by norm_num⟩
  | 3 => ⟨((-575918221/2147483648), (-475208881/2147483648)), (169/4294967296), by norm_num⟩
  | 4 => ⟨((237266563/1073741824), (783105475/4294967296)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((-156398377/1073741824), (-516197579/4294967296)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((171821179/2147483648), (141775251/2147483648)), (53/4294967296), by norm_num⟩
  | 7 => ⟨((-647193801/17179869184), (-133505171/4294967296)), (51/8589934592), by norm_num⟩
  | 8 => ⟨((533261297/34359738368), (880022529/68719476736)), (85/34359738368), by norm_num⟩
  | 9 => ⟨((-781129885/137438953472), (-322267855/68719476736)), (63/68719476736), by norm_num⟩
  | 10 => ⟨((1029790669/549755813888), (424856911/274877906944)), (21/68719476736), by norm_num⟩
  | 11 => ⟨((-308547459/549755813888), (-127296279/274877906944)), (103/1099511627776), by norm_num⟩
  | 12 => ⟨((169487015/1099511627776), (279698513/2199023255552)), (115/4398046511104), by norm_num⟩
  | 13 => ⟨((-687509603/17592186044416), (-283643283/8796093022208)), (59/8796093022208), by norm_num⟩
  | 14 => ⟨((323702785/35184372088832), (267097711/35184372088832)), (113/70368744177664), by norm_num⟩
  | 15 => ⟨((-142249543/70368744177664), (-117374731/70368744177664)), (201/562949953421312), by norm_num⟩
  | 16 => ⟨((58603911/140737488355328), (773695931/2251799813685248)), (167/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (898644319543/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777585240568609/633825300114114700748351602688), (132768849281/79228162514264337593543950336)), (92305/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888410680640125/39614081257132168796771975168), (597314089023/19807040628566084398385987584)), (103851/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888102936147301/2475880078570760549798248448), (634462305289/1237940039285380274899124224)), (110349/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884884806634997/77371252455336267181195264), (634255515307/77371252455336267181195264)), (55179/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774110811279177/4835703278458516698824704), (1188789849561/9671406556917033397649408)), (51735/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628811905067923/302231454903657293676544), (1039752087305/604462909807314587353088)), (45273/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471474994090909/18889465931478580854784), (844387202929/37778931862957161709568)), (147153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296121145530463/4722366482869645213696), (316465339333/1180591620717411303424)), (110381/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202437393583651/73786976294838206464), (1739391102289/590295810358705651712)), (75899/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821040219693407/73786976294838206464), (2172487946117/73786976294838206464)), (94893/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819920666210643/9223372036854775808), (305205473191/1152921504606846976)), (213561/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591172252595785/1152921504606846976), (2438640905261/1152921504606846976)), (213625/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596061158362829/72057594037927936), (266304680413/18014398509481984)), (46749/36028797018963968), by norm_num⟩
  | 4 => ⟨((371989161010207/9007199254740992), (3188921677185/36028797018963968)), (4385/562949953421312), by norm_num⟩
  | 3 => ⟨((742334403219307/4503599627370496), (3974394163033/9007199254740992)), (175529/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109403229370793/2251799813685248), (1978405986753/1125899906842624)), (702893/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101240648072237/1125899906842624), (11782906783173/2251799813685248)), (1056297/2251799813685248), by norm_num⟩
  | 0 => ⟨((67307693051349/70368744177664), (11608989295909/1125899906842624)), (2120499/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((67307693051349/70368744177664), (11608989295909/1125899906842624)), (8089061745650481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029957071278663/1125899906842624), (22207992974627/1125899906842624)), (4100243/2251799813685248), by norm_num⟩
  | 2 => ⟨((1883503795108083/2251799813685248), (10157776576813/281474976710656)), (478965/140737488355328), by norm_num⟩
  | 3 => ⟨((1572512342112885/2251799813685248), (67971266774291/1125899906842624)), (13373185/2251799813685248), by norm_num⟩
  | 4 => ⟨((1089934673035195/2251799813685248), (47466766478097/562949953421312)), (10146321/1125899906842624), by norm_num⟩
  | 5 => ⟨((511549952960059/2251799813685248), (367604077676323/4503599627370496)), (11533245/1125899906842624), by norm_num⟩
  | 6 => ⟨((809664033214025/18014398509481984), (668080164143877/18014398509481984)), (113966295/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1042569323/16777216)), (1/16777216), by norm_num⟩, -10, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile009Terms3

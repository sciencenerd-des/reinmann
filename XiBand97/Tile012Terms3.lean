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
namespace Reinmann.XiBand97.Tile012Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25387/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25387/1280))
  have he : value ((69/80), (25387/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-514276031/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((56873748918235/18014398509481984), (625607595919491/9007199254740992)), (6267563/562949953421312), by norm_num⟩
  | 1 => ⟨((-41913789/4294967296), (-1844195975/8589934592)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((64778651/4294967296), (1425122013/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-8343065/536870912), (-1468370881/4294967296)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((805899/67108864), (1134699183/4294967296)), (47/1073741824), by norm_num⟩
  | 5 => ⟨((-63771341/8589934592), (-1402961339/8589934592)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((65706641/17179869184), (722768843/8589934592)), (61/4294967296), by norm_num⟩
  | 7 => ⟨((-14507287/8589934592), (-159579227/4294967296)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((2802665/4294967296), (1973064661/137438953472)), (337/137438953472), by norm_num⟩
  | 9 => ⟨((-15401167/68719476736), (-1355294807/274877906944)), (233/274877906944), by norm_num⟩
  | 10 => ⟨((38084529/549755813888), (837854757/549755813888)), (145/549755813888), by norm_num⟩
  | 11 => ⟨((-85615197/4398046511104), (-1883523363/4398046511104)), (41/549755813888), by norm_num⟩
  | 12 => ⟨((88213403/17592186044416), (1940683559/17592186044416)), (85/4398046511104), by norm_num⟩
  | 13 => ⟨((-20974721/17592186044416), (-922882349/35184372088832)), (163/35184372088832), by norm_num⟩
  | 14 => ⟨((37047859/140737488355328), (1630096297/281474976710656)), (145/140737488355328), by norm_num⟩
  | 15 => ⟨((-61075469/1125899906842624), (-1343652495/1125899906842624)), (241/1125899906842624), by norm_num⟩
  | 16 => ⟨((47196717/4503599627370496), (519160863/2251799813685248)), (47/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (124185522437/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888927438375115/316912650057057350374175801344), (2349178626365/633825300114114700748351602688)), (5777/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888713819905225/39614081257132168796771975168), (2642215307381/39614081257132168796771975168)), (104001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944212378894801/1237940039285380274899124224), (2806590279855/2475880078570760549798248448)), (55259/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770091138385209/154742504910672534362390528), (350716466241/19342813113834066795298816)), (55269/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548522737505141/9671406556917033397649408), (2629461619115/9671406556917033397649408)), (51825/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257886971103481/604462909807314587353088), (1149933706055/302231454903657293676544)), (45357/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886327023546017/75557863725914323419136), (3735576265989/75557863725914323419136)), (147449/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648220457852901/2361183241434822606848), (1400094123867/2361183241434822606848)), (110621/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619937996387393/590295810358705651712), (1923916326715/295147905179352825856)), (76079/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113849220411565/4611686018427387904), (2403077066063/36893488147419103232)), (23785/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455133666651863/2305843009213693952), (2700963586523/4611686018427387904)), (214179/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397946026797923/288230376151711744), (2697844104833/576460752303423488)), (214321/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596327640494369/72057594037927936), (2357108514727/72057594037927936)), (187691/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488751287185803/36028797018963968), (7057326910807/36028797018963968)), (140929/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485653735584233/9007199254740992), (1099651216213/1125899906842624)), (176443/4503599627370496), by norm_num⟩
  | 2 => ⟨((138796957244323/281474976710656), (2190158398767/562949953421312)), (88433/562949953421312), by norm_num⟩
  | 1 => ⟨((2205336508733181/2251799813685248), (26099699178325/2251799813685248)), (266361/562949953421312), by norm_num⟩
  | 0 => ⟨((2159310874734827/2251799813685248), (51474654076857/2251799813685248)), (536991/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159310874734827/2251799813685248), (51474654076857/2251799813685248)), (2048458101512718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2069444088863893/2251799813685248), (98720836235851/2251799813685248)), (4217683/2251799813685248), by norm_num⟩
  | 2 => ⟨((1897527927419863/2251799813685248), (181452409538691/2251799813685248)), (4061033/1125899906842624), by norm_num⟩
  | 3 => ⟨((1584371415579843/2251799813685248), (152904806415185/1125899906842624)), (234335/35184372088832), by norm_num⟩
  | 4 => ⟨((536618141745885/1125899906842624), (430336663351107/2251799813685248)), (25177973/2251799813685248), by norm_num⟩
  | 5 => ⟨((858554539799051/4503599627370496), (820415595415353/4503599627370496)), (67247399/4503599627370496), by norm_num⟩
  | 6 => ⟨((56873748918235/18014398509481984), (625607595919491/9007199254740992)), (6267563/562949953421312), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-514276031/8388608)), (1/16777216), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-130417937/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((482073681038639/9007199254740992), (723462354165889/18014398509481984)), (7922163/1125899906842624), by norm_num⟩
  | 1 => ⟨((-720758075/4294967296), (-135207893/1073741824)), (3/134217728), by norm_num⟩
  | 2 => ⟨((1129966387/4294967296), (847887133/4294967296)), (153/4294967296), by norm_num⟩
  | 3 => ⟨((-1181001023/4294967296), (-443090867/2147483648)), (81/2147483648), by norm_num⟩
  | 4 => ⟨((925755469/4294967296), (694654425/4294967296)), (129/4294967296), by norm_num⟩
  | 5 => ⟨((-1161080367/8589934592), (-871233973/8589934592)), (41/2147483648), by norm_num⟩
  | 6 => ⟨((606760129/8589934592), (227645757/4294967296)), (87/8589934592), by norm_num⟩
  | 7 => ⟨((-1087138785/34359738368), (-815750805/34359738368)), (79/17179869184), by norm_num⟩
  | 8 => ⟨((852179343/68719476736), (639445483/68719476736)), (63/34359738368), by norm_num⟩
  | 9 => ⟨((-1187557067/274877906944), (-891101161/274877906944)), (89/137438953472), by norm_num⟩
  | 10 => ⟨((744715663/549755813888), (558808507/549755813888)), (113/549755813888), by norm_num⟩
  | 11 => ⟨((-212277423/549755813888), (-159285531/549755813888)), (65/1099511627776), by norm_num⟩
  | 12 => ⟨((887459509/8796093022208), (665918481/8796093022208)), (69/4398046511104), by norm_num⟩
  | 13 => ⟨((-53512003/2199023255552), (-642456475/35184372088832)), (135/35184372088832), by norm_num⟩
  | 14 => ⟨((767024347/140737488355328), (2248235/549755813888)), (123/140737488355328), by norm_num⟩
  | 15 => ⟨((-641333441/562949953421312), (-240617057/281474976710656)), (13/70368744177664), by norm_num⟩
  | 16 => ⟨((1005448647/4503599627370496), (377226695/2251799813685248)), (165/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (52408513005/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888899132813945/316912650057057350374175801344), (991332631987/633825300114114700748351602688)), (46149/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888650280833769/39614081257132168796771975168), (69686850357/2475880078570760549798248448)), (51921/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888357445115713/2475880078570760549798248448), (592174913101/1237940039285380274899124224)), (27585/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442506011938393/38685626227668133590597632), (591991278455/77371252455336267181195264)), (110347/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548460075775119/9671406556917033397649408), (1109593581671/9671406556917033397649408)), (25865/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314458094405261/151115727451828646838272), (121313062073/75557863725914323419136)), (11317/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886238750321303/75557863725914323419136), (1576339146277/75557863725914323419136)), (147137/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648187548193423/2361183241434822606848), (590807704779/2361183241434822606848)), (110367/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619848120605241/590295810358705651712), (1623683602301/590295810358705651712)), (75889/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455369029774925/18446744073709551616), (1014024681213/36893488147419103232)), (189757/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820410619574235/9223372036854775808), (1139709612535/4611686018427387904)), (106763/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49739427020865/36028797018963968), (569187963263/288230376151711744)), (213587/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192549944082547/144115188075855872), (62161287971/4503599627370496)), (186957/144115188075855872), by norm_num⟩
  | 4 => ⟨((93037304408109/2251799813685248), (2977758837587/36028797018963968)), (280571/36028797018963968), by norm_num⟩
  | 3 => ⟨((742733484142531/4503599627370496), (3711751518587/9007199254740992)), (350955/9007199254740992), by norm_num⟩
  | 2 => ⟨((555099108843991/1125899906842624), (7392254524499/4503599627370496)), (351317/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102425225943499/1125899906842624), (5505291785125/1125899906842624)), (1055775/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158521601819393/2251799813685248), (21711905177443/2251799813685248)), (1059457/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158521601819393/2251799813685248), (21711905177443/2251799813685248)), (4041507725242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2068897985682893/2251799813685248), (41625029061057/2251799813685248)), (4103143/2251799813685248), by norm_num⟩
  | 2 => ⟨((1900082860881013/2251799813685248), (76488094772043/2251799813685248)), (7691429/2251799813685248), by norm_num⟩
  | 3 => ⟨((800351884671517/1125899906842624), (32270567981785/562949953421312)), (13502671/2251799813685248), by norm_num⟩
  | 4 => ⟨((141308649462997/281474976710656), (5734925846133/70368744177664)), (10372473/1125899906842624), by norm_num⟩
  | 5 => ⟨((276286079123421/1125899906842624), (368524809385913/4503599627370496)), (48420977/4503599627370496), by norm_num⟩
  | 6 => ⟨((482073681038639/9007199254740992), (723462354165889/18014398509481984)), (7922163/1125899906842624), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-130417937/2097152)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-528752657/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((142337745374103/2251799813685248), (-14454470141449/1125899906842624)), (21809975/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1725605075/8589934592), (350472139/8589934592)), (133/4294967296), by norm_num⟩
  | 2 => ⟨((685508227/2147483648), (-278454831/4294967296)), (213/4294967296), by norm_num⟩
  | 3 => ⟨((-1452388031/4294967296), (294981481/4294967296)), (57/1073741824), by norm_num⟩
  | 4 => ⟨((288485459/1073741824), (-58591689/1073741824)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((-1466915709/8589934592), (297932067/8589934592)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((1553979029/17179869184), (-78903679/4294967296)), (251/17179869184), by norm_num⟩
  | 7 => ⟨((-705518429/17179869184), (35822877/4294967296)), (115/17179869184), by norm_num⟩
  | 8 => ⟨((1121087773/68719476736), (-227694063/68719476736)), (23/8589934592), by norm_num⟩
  | 9 => ⟨((-791750509/137438953472), (160805331/137438953472)), (131/137438953472), by norm_num⟩
  | 10 => ⟨((1006490295/549755813888), (-204419199/549755813888)), (21/68719476736), by norm_num⟩
  | 11 => ⟨((-581578243/1099511627776), (236238261/2199023255552)), (49/549755813888), by norm_num⟩
  | 12 => ⟨((308047827/2199023255552), (-250259303/8796093022208)), (105/4398046511104), by norm_num⟩
  | 13 => ⟨((-301228485/8796093022208), (122359621/17592186044416)), (207/35184372088832), by norm_num⟩
  | 14 => ⟨((1094080389/140737488355328), (-55552209/35184372088832)), (95/70368744177664), by norm_num⟩
  | 15 => ⟨((-927212365/562949953421312), (188317771/562949953421312)), (163/562949953421312), by norm_num⟩
  | 16 => ⟨((368341351/1125899906842624), (-299242007/4503599627370496)), (261/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-261011483277/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888871107355235/316912650057057350374175801344), (-38569221367/79228162514264337593543950336)), (184461/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944293632208823/19807040628566084398385987584), (-1355629913/154742504910672534362390528)), (207523/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888290543804493/2475880078570760549798248448), (-92157076449/618970019642690137449562112)), (110249/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769957206717881/154742504910672534362390528), (-184256229467/77371252455336267181195264)), (220503/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548397476303181/9671406556917033397649408), (-345357394399/9671406556917033397649408)), (25841/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628888833516435/302231454903657293676544), (-37758092769/75557863725914323419136)), (45223/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886149965416759/75557863725914323419136), (-122656186331/18889465931478580854784)), (36745/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296308612430033/4722366482869645213696), (-91941757201/1180591620717411303424)), (220479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619756875141485/590295810358705651712), (-505352408323/590295810358705651712)), (303173/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56917572402911/2305843009213693952), (-631200028633/73786976294838206464)), (189495/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910141470821711/4611686018427387904), (-709426273479/9223372036854775808)), (213197/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795767211422321/576460752303423488), (-177146263635/288230376151711744)), (213217/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192439096967115/144115188075855872), (-619066896461/144115188075855872)), (186587/72057594037927936), by norm_num⟩
  | 4 => ⟨((744215787984151/18014398509481984), (-926713649577/36028797018963968)), (279925/18014398509481984), by norm_num⟩
  | 3 => ⟨((742631025943959/4503599627370496), (-1155097885391/9007199254740992)), (349985/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219991682515195/4503599627370496), (-2300343329183/4503599627370496)), (350105/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102127966809875/1125899906842624), (-3425988878005/2251799813685248)), (2101853/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157382479483837/2251799813685248), (-6754500667757/2251799813685248)), (2104365/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157382479483837/2251799813685248), (-6754500667757/2251799813685248)), (8027515415671920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516725944200109/562949953421312), (-6471286350465/1125899906842624)), (1011221/281474976710656), by norm_num⟩
  | 2 => ⟨((1897115225963381/2251799813685248), (-11879853721671/1125899906842624)), (1868003/281474976710656), by norm_num⟩
  | 3 => ⟨((399511718916423/562949953421312), (-20017277948625/1125899906842624)), (1593481/140737488355328), by norm_num⟩
  | 4 => ⟨((566691371863601/1125899906842624), (-56823076884051/2251799813685248)), (9273477/562949953421312), by norm_num⟩
  | 5 => ⟨((569023753321587/2251799813685248), (-114401456815947/4503599627370496)), (78425065/4503599627370496), by norm_num⟩
  | 6 => ⟨((142337745374103/2251799813685248), (-14454470141449/1125899906842624)), (21809975/2251799813685248), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-528752657/8388608)), (1/8388608), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-535544467/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((596594109946755/18014398509481984), (-949947899984827/18014398509481984)), (291820803/18014398509481984), by norm_num⟩
  | 1 => ⟨((-457850065/4294967296), (729027827/4294967296)), (225/4294967296), by norm_num⟩
  | 2 => ⟨((736881253/4294967296), (-36666407/134217728)), (91/1073741824), by norm_num⟩
  | 3 => ⟨((-197660771/1073741824), (1258929185/4294967296)), (49/536870912), by norm_num⟩
  | 4 => ⟨((636245477/4294967296), (-253271045/1073741824)), (317/4294967296), by norm_num⟩
  | 5 => ⟨((-409599037/4294967296), (652198435/4294967296)), (205/4294967296), by norm_num⟩
  | 6 => ⟨((439482813/8589934592), (-699781925/8589934592)), (111/4294967296), by norm_num⟩
  | 7 => ⟨((-808366059/34359738368), (321787303/8589934592)), (411/34359738368), by norm_num⟩
  | 8 => ⟨((650507491/68719476736), (-1035793371/68719476736)), (333/68719476736), by norm_num⟩
  | 9 => ⟨((-232655871/68719476736), (740908943/137438953472)), (15/8589934592), by norm_num⟩
  | 10 => ⟨((599112287/549755813888), (-476978777/274877906944)), (311/549755813888), by norm_num⟩
  | 11 => ⟨((-87657639/274877906944), (1116607603/2199023255552)), (183/1099511627776), by norm_num⟩
  | 12 => ⟨((752424147/8796093022208), (-299518435/2199023255552)), (395/8796093022208), by norm_num⟩
  | 13 => ⟨((-372609215/17592186044416), (148325023/4398046511104)), (393/35184372088832), by norm_num⟩
  | 14 => ⟨((685361597/140737488355328), (-545645521/70368744177664)), (363/140737488355328), by norm_num⟩
  | 15 => ⟨((-147072925/140737488355328), (468364047/281474976710656)), (157/281474976710656), by norm_num⟩
  | 16 => ⟨((473409483/2251799813685248), (-376901427/1125899906842624)), (127/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-328916724063/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222210844012915/79228162514264337593543950336), (-194402542163/79228162514264337593543950336)), (92353/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888524815661023/39614081257132168796771975168), (-874602365593/19807040628566084398385987584)), (207815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888224118910679/2475880078570760549798248448), (-929001959195/1237940039285380274899124224)), (110413/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769890699716657/154742504910672534362390528), (-464353087143/38685626227668133590597632)), (55213/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387083759708477/2417851639229258349412352), (-870347894399/4835703278458516698824704)), (51769/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157215368398213/75557863725914323419136), (-380620203535/151115727451828646838272)), (181219/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235757610328055/9444732965739290427392), (-1236427215203/37778931862957161709568)), (73633/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162030207234343/590295810358705651712), (-926805825433/2361183241434822606848)), (13809/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619664581502485/590295810358705651712), (-636761189195/147573952589676412928)), (303871/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910623301904695/36893488147419103232), (-795325261727/18446744073709551616)), (379949/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820152289685969/9223372036854775808), (-446940335215/1152921504606846976)), (213797/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591403179051609/1152921504606846976), (-3571226292003/1152921504606846976)), (427783/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192323595011221/144115188075855872), (-194999764701/9007199254740992)), (93631/36028797018963968), by norm_num⟩
  | 4 => ⟨((93016062574533/2251799813685248), (-2335178729387/18014398509481984)), (140553/9007199254740992), by norm_num⟩
  | 3 => ⟨((742520766190561/4503599627370496), (-727639956009/1125899906842624)), (703515/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219543788957031/4503599627370496), (-5795953499951/2251799813685248)), (1409285/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203567126103405/2251799813685248), (-17262550596293/2251799813685248)), (2119595/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077969002222875/1125899906842624), (-8506743722193/562949953421312)), (33297/17592186044416), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077969002222875/1125899906842624), (-8506743722193/562949953421312)), (127017974920624489/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((2063642964952735/2251799813685248), (-254518796105/8796093022208)), (8289961/2251799813685248), by norm_num⟩
  | 2 => ⟨((118082679097925/140737488355328), (-119424822294223/2251799813685248)), (7837139/1125899906842624), by norm_num⟩
  | 3 => ⟨((789430432618041/1125899906842624), (-200401515361583/2251799813685248)), (13982447/1125899906842624), by norm_num⟩
  | 4 => ⟨((272297835880987/562949953421312), (-140512539354281/1125899906842624)), (1381031/70368744177664), by norm_num⟩
  | 5 => ⟨((983535642213295/4503599627370496), (-543725212485139/4503599627370496)), (53782725/2251799813685248), by norm_num⟩
  | 6 => ⟨((596594109946755/18014398509481984), (-949947899984827/18014398509481984)), (291820803/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-535544467/8388608)), (1/8388608), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-271034931/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-116800634670041/9007199254740992), (-1058980224963757/18014398509481984)), (186663595/9007199254740992), by norm_num⟩
  | 1 => ⟨((362918609/8589934592), (1645212081/8589934592)), (291/4294967296), by norm_num⟩
  | 2 => ⟨((-147802983/2147483648), (-1340064947/4294967296)), (119/1073741824), by norm_num⟩
  | 3 => ⟨((40129699/536870912), (1455353655/4294967296)), (519/4294967296), by norm_num⟩
  | 4 => ⟨((-261492867/4294967296), (-296355169/1073741824)), (425/4294967296), by norm_num⟩
  | 5 => ⟨((170393801/4294967296), (96555375/536870912)), (139/2147483648), by norm_num⟩
  | 6 => ⟨((-185053151/8589934592), (-838897955/8589934592)), (303/8589934592), by norm_num⟩
  | 7 => ⟨((344526303/34359738368), (1561834585/34359738368)), (283/17179869184), by norm_num⟩
  | 8 => ⟨((-280624989/68719476736), (-318037991/17179869184)), (463/68719476736), by norm_num⟩
  | 9 => ⟨((12698657/8589934592), (921065313/137438953472)), (337/137438953472), by norm_num⟩
  | 10 => ⟨((-264790083/549755813888), (-1200367883/549755813888)), (441/549755813888), by norm_num⟩
  | 11 => ⟨((19607083/137438953472), (1422150707/2199023255552)), (131/549755813888), by norm_num⟩
  | 12 => ⟨((-340702769/8796093022208), (-193062679/1099511627776)), (571/8796093022208), by norm_num⟩
  | 13 => ⟨((170775771/17592186044416), (193543645/4398046511104)), (287/17592186044416), by norm_num⟩
  | 14 => ⟨((-317945113/140737488355328), (-720667291/70368744177664)), (537/140737488355328), by norm_num⟩
  | 15 => ⟨((276238899/562949953421312), (626134295/281474976710656)), (117/140737488355328), by norm_num⟩
  | 16 => ⟨((-112501625/1125899906842624), (-510001495/1125899906842624)), (383/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-2328952479705/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777631897197277/633825300114114700748351602688), (-2752848631047/633825300114114700748351602688)), (92471/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888462967813827/39614081257132168796771975168), (-3096201324859/39614081257132168796771975168)), (208095/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944079110279465/1237940039285380274899124224), (-3288770786125/2475880078570760549798248448)), (110571/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884912296750331/77371252455336267181195264), (-3287710237575/154742504910672534362390528)), (55297/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548272843601225/9671406556917033397649408), (-96284435449/302231454903657293676544)), (51853/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157208538240975/75557863725914323419136), (-2694838251095/604462909807314587353088)), (90767/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471492919438753/18889465931478580854784), (-4377002020115/75557863725914323419136)), (147541/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648087196739845/2361183241434822606848), (-1640453073159/2361183241434822606848)), (13837/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619571507649487/590295810358705651712), (-4508249104567/590295810358705651712)), (152271/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821129385097329/73786976294838206464), (-5630819394731/73786976294838206464)), (47609/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820019216136659/9223372036854775808), (-3164250335611/4611686018427387904)), (428747/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591268606192503/1152921504606846976), (-3160397364747/576460752303423488)), (429081/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192204162269131/144115188075855872), (-2761018592129/72057594037927936)), (375823/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488074502152355/36028797018963968), (-8265766788993/36028797018963968)), (282243/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484807575499393/9007199254740992), (-5151007185839/4503599627370496)), (44183/562949953421312), by norm_num⟩
  | 2 => ⟨((554764623178221/1125899906842624), (-20513692437409/4503599627370496)), (44307/140737488355328), by norm_num⟩
  | 1 => ⟨((2202796132416641/2251799813685248), (-3818194644275/281474976710656)), (267087/281474976710656), by norm_num⟩
  | 0 => ⟨((1077113123393183/1125899906842624), (-30098164471485/1125899906842624)), (4313433/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077113123393183/1125899906842624), (-30098164471485/1125899906842624)), (16454441079146575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2059271475263219/2251799813685248), (-28793969823833/562949953421312)), (8483671/2251799813685248), by norm_num⟩
  | 2 => ⟨((1877313205183607/2251799813685248), (-210656739049175/2251799813685248)), (16384491/2251799813685248), by norm_num⟩
  | 3 => ⟨((1545398746149969/2251799813685248), (-351246745447339/2251799813685248)), (30384873/2251799813685248), by norm_num⟩
  | 4 => ⟨((502905052804825/1125899906842624), (-120529426440269/562949953421312)), (51185131/2251799813685248), by norm_num⟩
  | 5 => ⟨((346041633720061/2251799813685248), (-430694467244157/2251799813685248)), (135286949/4503599627370496), by norm_num⟩
  | 6 => ⟨((-116800634670041/9007199254740992), (-1058980224963757/18014398509481984)), (186663595/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-271034931/4194304)), (1/8388608), by norm_num⟩, -10, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-137087239/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-431646879135119/9007199254740992), (-74646127592811/2251799813685248)), (192502577/18014398509481984), by norm_num⟩
  | 1 => ⟨((678366517/4294967296), (234624347/2147483648)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((-69868293/268435456), (-193320893/1073741824)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((307032661/1073741824), (849538835/4294967296)), (141/2147483648), by norm_num⟩
  | 4 => ⟨((-1011929563/4294967296), (-699985353/4294967296)), (117/2147483648), by norm_num⟩
  | 5 => ⟨((83378869/536870912), (230703753/2147483648)), (39/1073741824), by norm_num⟩
  | 6 => ⟨((-732808401/8589934592), (-126726989/2147483648)), (173/8589934592), by norm_num⟩
  | 7 => ⟨((21564437/536870912), (477338837/17179869184)), (41/4294967296), by norm_num⟩
  | 8 => ⟨((-1137165863/68719476736), (-196653867/17179869184)), (17/4294967296), by norm_num⟩
  | 9 => ⟨((416434797/68719476736), (576123613/137438953472)), (201/137438953472), by norm_num⟩
  | 10 => ⟨((-1098000925/549755813888), (-759523777/549755813888)), (267/549755813888), by norm_num⟩
  | 11 => ⟨((657969441/1099511627776), (455139357/1099511627776)), (81/549755813888), by norm_num⟩
  | 12 => ⟨((-722853313/4398046511104), (-500021691/4398046511104)), (45/1099511627776), by norm_num⟩
  | 13 => ⟨((91631023/2199023255552), (253536911/8796093022208)), (23/2199023255552), by norm_num⟩
  | 14 => ⟨((-172571945/17592186044416), (-119373757/17592186044416)), (175/70368744177664), by norm_num⟩
  | 15 => ⟨((303343455/140737488355328), (839331049/562949953421312)), (155/281474976710656), by norm_num⟩
  | 16 => ⟨((-499885271/1125899906842624), (-691574553/2251799813685248)), (257/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-825997901033/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777577662044397/633825300114114700748351602688), (-3905146040761/633825300114114700748351602688)), (92585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888401744257357/39614081257132168796771975168), (-4392198910303/39614081257132168796771975168)), (104183/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888092886360877/2475880078570760549798248448), (-583169603855/309485009821345068724781056)), (110723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13826241718903/1208925819614629174706176), (-4663833497527/154742504910672534362390528)), (27689/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387052738633337/2417851639229258349412352), (-4370725881897/9671406556917033397649408)), (25967/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257613814411629/604462909807314587353088), (-1911383854329/302231454903657293676544)), (90919/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942941247469245/37778931862957161709568), (-6208966071183/75557863725914323419136)), (147807/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296106952264895/4722366482869645213696), (-4654073270561/4722366482869645213696)), (1733/73786976294838206464), by norm_num⟩
  | 9 => ⟨((404869469236071/147573952589676412928), (-399690296133/36893488147419103232)), (152595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227626375072339/9223372036854775808), (-3993675489153/36893488147419103232)), (190881/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819884186534619/9223372036854775808), (-4488450456177/4611686018427387904)), (107465/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397782818422211/288230376151711744), (-8965824651663/1152921504606846976)), (107583/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192081413624161/144115188075855872), (-7832649400773/144115188075855872)), (188537/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487885233886241/36028797018963968), (-11724113805939/36028797018963968)), (283339/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484562031030733/9007199254740992), (-14611713294917/9007199254740992)), (177555/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218540706361977/4503599627370496), (-29093445697569/4503599627370496)), (713031/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201953336856841/2251799813685248), (-5414535787287/281474976710656)), (538301/1125899906842624), by norm_num⟩
  | 0 => ⟨((2152279936739399/2251799813685248), (-85343455443409/2251799813685248)), (1090779/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152279936739399/2251799813685248), (-85343455443409/2251799813685248)), (4160991672996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1026961942308431/1125899906842624), (-40785820694747/562949953421312)), (4335649/2251799813685248), by norm_num⟩
  | 2 => ⟨((1861616457913813/2251799813685248), (-148807137774017/1125899906842624)), (8537549/2251799813685248), by norm_num⟩
  | 3 => ⟨((1499707726611273/2251799813685248), (-492089598820581/2251799813685248)), (2046645/281474976710656), by norm_num⟩
  | 4 => ⟨((27852318951057/70368744177664), (-655467301357031/2251799813685248)), (14482645/1125899906842624), by norm_num⟩
  | 5 => ⟨((80986845653269/1125899906842624), (-518874808772825/2251799813685248)), (39792007/2251799813685248), by norm_num⟩
  | 6 => ⟨((-431646879135119/9007199254740992), (-74646127592811/2251799813685248)), (192502577/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-137087239/2097152)), (1/16777216), by norm_num⟩, -10, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile012Terms3

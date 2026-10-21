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
namespace Reinmann.XiBand58.Tile000Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4561/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4561/320))
  have he : value ((15/16), (4561/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-1326005843/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-82212412099013/4503599627370496), (-1297916235484415/18014398509481984)), (231235191/18014398509481984), by norm_num⟩
  | 1 => ⟨((108690837/2147483648), (428985109/2147483648)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((-301354989/4294967296), (-1189399275/4294967296)), (217/4294967296), by norm_num⟩
  | 3 => ⟨((69627787/1073741824), (1099238339/4294967296)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((-193049217/4294967296), (-1523867911/8589934592)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((214098433/8589934592), (845011797/8589934592)), (315/17179869184), by norm_num⟩
  | 6 => ⟨((-197868967/17179869184), (-390478363/8589934592)), (293/34359738368), by norm_num⟩
  | 7 => ⟨((313491009/68719476736), (618649089/34359738368)), (117/34359738368), by norm_num⟩
  | 8 => ⟨((-217295409/137438953472), (-53601859/8589934592)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((4183825/8589934592), (1056824247/549755813888)), (51/137438953472), by norm_num⟩
  | 10 => ⟨((-148480333/1099511627776), (-293013899/549755813888)), (57/549755813888), by norm_num⟩
  | 11 => ⟨((299399925/8796093022208), (1181682955/8796093022208)), (29/1099511627776), by norm_num⟩
  | 12 => ⟨((-276704285/35184372088832), (-1092106945/35184372088832)), (27/4398046511104), by norm_num⟩
  | 13 => ⟨((118028797/70368744177664), (465840523/70368744177664)), (93/70368744177664), by norm_num⟩
  | 14 => ⟨((-186997321/562949953421312), (-738048103/562949953421312)), (297/1125899906842624), by norm_num⟩
  | 15 => ⟨((138257777/2251799813685248), (272840513/1125899906842624)), (111/2251799813685248), by norm_num⟩
  | 16 => ⟨((-383331953/36028797018963968), (-1512949059/36028797018963968)), (155/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (-2369374751719/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111122274389797/39614081257132168796771975168), (-2801603766933/633825300114114700748351602688)), (92477/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944413963622417/19807040628566084398385987584), (-3151090765167/39614081257132168796771975168)), (52027/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888545872267197/2475880078570760549798248448), (-3347145890579/2475880078570760549798248448)), (55289/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770212112843007/154742504910672534362390528), (-3346147210843/154742504910672534362390528)), (110601/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387159000596523/2417851639229258349412352), (-3135952266613/9671406556917033397649408)), (103713/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314496482327785/151115727451828646838272), (-2742897887525/604462909807314587353088)), (45387/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886487552311251/75557863725914323419136), (-4455221763957/75557863725914323419136)), (147553/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296561068981369/4722366482869645213696), (-3339678277327/4722366482869645213696)), (110705/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810051406109539/295147905179352825856), (-4589234890355/590295810358705651712)), (38071/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821792954756459/73786976294838206464), (-5732312270771/73786976294838206464)), (95227/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910382480533681/4611686018427387904), (-3221518853375/4611686018427387904)), (53599/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592013388221297/1152921504606846976), (-6435777451537/1152921504606846976)), (107283/576460752303423488), by norm_num⟩
  | 5 => ⟨((596427382167801/72057594037927936), (-1405786686599/36028797018963968)), (187937/144115188075855872), by norm_num⟩
  | 4 => ⟨((744524121737371/18014398509481984), (-2104606552435/9007199254740992)), (282287/36028797018963968), by norm_num⟩
  | 3 => ⟨((743010487491603/4503599627370496), (-1311821302709/1125899906842624)), (353529/9007199254740992), by norm_num⟩
  | 2 => ⟨((555368495985413/1125899906842624), (-2612995192529/562949953421312)), (709073/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206391183120411/2251799813685248), (-15571859884429/1125899906842624)), (1068665/2251799813685248), by norm_num⟩
  | 0 => ⟨((270163012876693/281474976710656), (-61442893289083/2251799813685248)), (2157643/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((270163012876693/281474976710656), (-61442893289083/2251799813685248)), (8230754860884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072768710700255/2251799813685248), (-117947231862841/2251799813685248)), (4259611/2251799813685248), by norm_num⟩
  | 2 => ⟨((475448411591405/562949953421312), (-217139490138689/2251799813685248)), (8288125/2251799813685248), by norm_num⟩
  | 3 => ⟨((396312928605419/562949953421312), (-366777277634637/2251799813685248)), (15598175/2251799813685248), by norm_num⟩
  | 4 => ⟨((1056265042848187/2251799813685248), (-516417404999835/2251799813685248)), (13521669/1125899906842624), by norm_num⟩
  | 5 => ⟨((377035693580083/2251799813685248), (-484477926594185/2251799813685248)), (37774747/2251799813685248), by norm_num⟩
  | 6 => ⟨((-82212412099013/4503599627370496), (-1297916235484415/18014398509481984)), (231235191/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-1326005843/33554432)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-1354999903/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-567135109520877/9007199254740992), (-279970362621923/9007199254740992)), (228263465/18014398509481984), by norm_num⟩
  | 1 => ⟨((95773623/536870912), (2954959/33554432)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((-1085388427/4294967296), (-535809873/4294967296)), (223/4294967296), by norm_num⟩
  | 3 => ⟨((512522829/2147483648), (506021227/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-726043259/4294967296), (-358416523/4294967296)), (19/536870912), by norm_num⟩
  | 5 => ⟨((205703545/2147483648), (203094095/4294967296)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((-194267343/4294967296), (-383605933/17179869184)), (83/8589934592), by norm_num⟩
  | 7 => ⟨((1258059037/68719476736), (310524985/34359738368)), (271/68719476736), by norm_num⟩
  | 8 => ⟨((-891087413/137438953472), (-219945883/68719476736)), (97/68719476736), by norm_num⟩
  | 9 => ⟨((1122062555/549755813888), (553914321/549755813888)), (247/549755813888), by norm_num⟩
  | 10 => ⟨((-635808521/1099511627776), (-313871489/1099511627776)), (141/1099511627776), by norm_num⟩
  | 11 => ⟨((81880963/549755813888), (646738103/8796093022208)), (293/8796093022208), by norm_num⟩
  | 12 => ⟨((-1237259931/35184372088832), (-610782341/35184372088832)), (279/35184372088832), by norm_num⟩
  | 13 => ⟨((67411949/8796093022208), (532454363/140737488355328)), (245/140737488355328), by norm_num⟩
  | 14 => ⟨((-873108267/562949953421312), (-215508115/281474976710656)), (25/70368744177664), by norm_num⟩
  | 15 => ⟨((659653865/2251799813685248), (81410729/562949953421312)), (305/4503599627370496), by norm_num⟩
  | 16 => ⟨((-467235033/9007199254740992), (-57663491/2251799813685248)), (109/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (-873737218549/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777863905497003/633825300114114700748351602688), (-4132120802263/633825300114114700748351602688)), (1447/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((944361817061347/19807040628566084398385987584), (-2323774633501/19807040628566084398385987584)), (52105/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888434726316891/2475880078570760549798248448), (-2468340630467/1237940039285380274899124224)), (110753/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885050295504575/77371252455336267181195264), (-4935174304637/154742504910672534362390528)), (110787/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548531051636991/9671406556917033397649408), (-4625125202057/9671406556917033397649408)), (25975/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257893698765541/604462909807314587353088), (-4045384329219/604462909807314587353088)), (22737/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235792116381505/9444732965739290427392), (-410671884395/4722366482869645213696)), (73929/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296447450569223/4722366482869645213696), (-2462719591925/2361183241434822606848)), (55477/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619945528191761/590295810358705651712), (-6768217742159/590295810358705651712)), (76329/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821594764365417/73786976294838206464), (-8453883862831/73786976294838206464)), (190967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455134955352291/2305843009213693952), (-4750920459631/4611686018427387904)), (107519/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591785535815683/1152921504606846976), (-1186359518265/144115188075855872)), (26911/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192652350684843/144115188075855872), (-2073048153893/36028797018963968)), (188659/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488738559979215/36028797018963968), (-12413669292947/36028797018963968)), (8861/1125899906842624), by norm_num⟩
  | 3 => ⟨((742811655503563/4503599627370496), (-7737033075347/4503599627370496)), (355429/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110323589663461/2251799813685248), (-30819326458863/4503599627370496)), (356915/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102536494806891/1125899906842624), (-45907869526997/2251799813685248)), (1078197/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079179990145025/1125899906842624), (-90536625054605/2251799813685248)), (1093169/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1079179990145025/1125899906842624), (-90536625054605/2251799813685248)), (4170108799460982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2065157344706753/2251799813685248), (-173559503008023/2251799813685248)), (68235/35184372088832), by norm_num⟩
  | 2 => ⟨((470151912658407/562949953421312), (-79586933128411/562949953421312)), (1085417/281474976710656), by norm_num⟩
  | 3 => ⟨((762798681291955/1125899906842624), (-531741034605761/2251799813685248)), (8479559/1125899906842624), by norm_num⟩
  | 4 => ⟨((454014333870351/1125899906842624), (-90063814181217/281474976710656)), (30989119/2251799813685248), by norm_num⟩
  | 5 => ⟨((33904064161411/562949953421312), (-1162171162187301/4503599627370496)), (89647393/4503599627370496), by norm_num⟩
  | 6 => ⟨((-567135109520877/9007199254740992), (-279970362621923/9007199254740992)), (228263465/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-1354999903/33554432)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-691168115/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1123723363695829/18014398509481984), (209004573074373/9007199254740992)), (106683391/9007199254740992), by norm_num⟩
  | 1 => ⟨((774378365/4294967296), (-72014441/1073741824)), (297/8589934592), by norm_num⟩
  | 2 => ⟨((-559560339/2147483648), (416297013/4294967296)), (27/536870912), by norm_num⟩
  | 3 => ⟨((539112467/2147483648), (-401084377/4294967296)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((-1558235449/8589934592), (289820739/4294967296)), (153/4294967296), by norm_num⟩
  | 5 => ⟨((900775947/8589934592), (-10471121/268435456)), (179/8589934592), by norm_num⟩
  | 6 => ⟨((-867859119/17179869184), (322831279/17179869184)), (87/8589934592), by norm_num⟩
  | 7 => ⟨((1433391707/68719476736), (-266600689/34359738368)), (145/34359738368), by norm_num⟩
  | 8 => ⟨((-1035758727/137438953472), (385287551/137438953472)), (211/137438953472), by norm_num⟩
  | 9 => ⟨((1330545677/549755813888), (-247472057/274877906944)), (273/549755813888), by norm_num⟩
  | 10 => ⟨((-1538308659/2199023255552), (143057249/549755813888)), (159/1099511627776), by norm_num⟩
  | 11 => ⟨((808415255/4398046511104), (-300719005/4398046511104)), (169/4398046511104), by norm_num⟩
  | 12 => ⟨((-1557747081/35184372088832), (579459813/35184372088832)), (41/4398046511104), by norm_num⟩
  | 13 => ⟨((1385374821/140737488355328), (-257669889/70368744177664)), (147/70368744177664), by norm_num⟩
  | 14 => ⟨((-1144070931/562949953421312), (212789077/281474976710656)), (245/562949953421312), by norm_num⟩
  | 15 => ⟨((881810749/2251799813685248), (-328021087/2251799813685248)), (95/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1274380443/18014398509481984), (474051443/18014398509481984)), (277/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (907095498813/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888890334528471/316912650057057350374175801344), (536187583261/79228162514264337593543950336)), (92623/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236078747138629/4951760157141521099596496896), (4824537439637/39614081257132168796771975168)), (26057/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944167595338731/1237940039285380274899124224), (5124651997529/2475880078570760549798248448)), (55387/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770001027246719/154742504910672534362390528), (5123055957091/154742504910672534362390528)), (110809/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774218840390377/4835703278458516698824704), (4801169625879/9671406556917033397649408)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628905984747795/302231454903657293676544), (2099664302231/302231454903657293676544)), (45485/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943102032645915/37778931862957161709568), (1705183073523/18889465931478580854784)), (147895/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((10127716817485/36893488147419103232), (2556385357207/2361183241434822606848)), (110983/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50619011399215/18446744073709551616), (7025546714891/590295810358705651712)), (76351/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821423192356251/73786976294838206464), (8775167464047/73786976294838206464)), (47757/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227543330208129/1152921504606846976), (9862766088709/9223372036854775808)), (107557/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795796077755847/576460752303423488), (9851153221131/1152921504606846976)), (107687/576460752303423488), by norm_num⟩
  | 5 => ⟨((596241459318611/72057594037927936), (8606706649271/144115188075855872)), (188745/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488483966707199/36028797018963968), (12883985280439/36028797018963968)), (283703/36028797018963968), by norm_num⟩
  | 3 => ⟨((742652148930281/4503599627370496), (8029709360499/4503599627370496)), (355655/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110003434217245/2251799813685248), (999450630531/140737488355328)), (357199/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102053458269805/1125899906842624), (47633537070885/2251799813685248)), (1079335/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156406031916485/2251799813685248), (11739050295359/281474976710656)), (547443/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2156406031916485/2251799813685248), (11739050295359/281474976710656)), (2088329317333030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((8051315578073/8796093022208), (11241744808769/140737488355328)), (4376663/2251799813685248), by norm_num⟩
  | 2 => ⟨((117015630275653/140737488355328), (329276499918935/2251799813685248)), (2177841/562949953421312), by norm_num⟩
  | 3 => ⟨((754262733421399/1125899906842624), (136887824357413/562949953421312)), (17033753/2251799813685248), by norm_num⟩
  | 4 => ⟨((877447741485853/2251799813685248), (733631001792863/2251799813685248)), (31106411/2251799813685248), by norm_num⟩
  | 5 => ⟨((12861938861021/281474976710656), (142935189374949/562949953421312)), (22255477/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1123723363695829/18014398509481984), (209004573074373/9007199254740992)), (106683391/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-691168115/16777216)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-11001517/262144)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-489606617676581/18014398509481984), (1029168510801443/18014398509481984)), (25523177/2251799813685248), by norm_num⟩
  | 1 => ⟨((687416463/8589934592), (-1444971027/8589934592)), (289/8589934592), by norm_num⟩
  | 2 => ⟨((-506013957/4294967296), (531828627/2147483648)), (107/2147483648), by norm_num⟩
  | 3 => ⟨((248321203/2147483648), (-130494745/536870912)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((-365583315/4294967296), (768467627/4294967296)), (79/2147483648), by norm_num⟩
  | 5 => ⟨((430575105/8589934592), (-452541207/4294967296)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((-105650177/4294967296), (222079995/4294967296)), (187/17179869184), by norm_num⟩
  | 7 => ⟨((355520571/34359738368), (-747315421/34359738368)), (159/34359738368), by norm_num⟩
  | 8 => ⟨((-261702157/68719476736), (137526541/17179869184)), (59/34359738368), by norm_num⟩
  | 9 => ⟨((5351153/4294967296), (-719890681/274877906944)), (311/549755813888), by norm_num⟩
  | 10 => ⟨((-403357273/1099511627776), (847869673/1099511627776)), (185/1099511627776), by norm_num⟩
  | 11 => ⟨((431876683/4398046511104), (-907818369/4398046511104)), (25/549755813888), by norm_num⟩
  | 12 => ⟨((-105969545/4398046511104), (55687829/1099511627776)), (99/8796093022208), by norm_num⟩
  | 13 => ⟨((48003209/8796093022208), (-100904255/8796093022208)), (181/70368744177664), by norm_num⟩
  | 14 => ⟨((-646137233/562949953421312), (84887549/35184372088832)), (307/562949953421312), by norm_num⟩
  | 15 => ⟨((507336441/2251799813685248), (-1066437155/2251799813685248)), (243/2251799813685248), by norm_num⟩
  | 16 => ⟨((-186727649/4503599627370496), (392507391/4503599627370496)), (45/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (2624554491343/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444426830177989/158456325028528675187087900672), (1551254179937/316912650057057350374175801344)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((29508558412043/618970019642690137449562112), (3489484579621/39614081257132168796771975168)), (104089/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888248182841189/2475880078570760549798248448), (1853266474559/1237940039285380274899124224)), (110617/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884957218078391/77371252455336267181195264), (231584902375/9671406556917033397649408)), (110643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548356944077775/9671406556917033397649408), (1736263025935/4835703278458516698824704)), (103755/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314435441732903/151115727451828646838272), (189825831255/37778931862957161709568)), (45407/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235761351767151/9444732965739290427392), (154160454189/2361183241434822606848)), (73811/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296263537949009/4722366482869645213696), (924451748505/1180591620717411303424)), (110761/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619693743990783/590295810358705651712), (317572825795/36893488147419103232)), (152369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910640837632885/36893488147419103232), (6346480810271/73786976294838206464)), (190571/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820189848978959/9223372036854775808), (7132954839057/9223372036854775808)), (214543/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795719186867699/576460752303423488), (3562209013653/576460752303423488)), (214731/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192351737737409/144115188075855872), (1556068308899/36028797018963968)), (188101/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488293928906195/36028797018963968), (9317253188535/36028797018963968)), (282575/36028797018963968), by norm_num⟩
  | 3 => ⟨((742539241606047/4503599627370496), (2903276544563/2251799813685248)), (176981/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219590233030425/4503599627370496), (23126086506991/4503599627370496)), (710157/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203568736774389/2251799813685248), (34439706309117/2251799813685248)), (1070841/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155672515887271/2251799813685248), (67887053190081/2251799813685248)), (135263/140737488355328), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2155672515887271/2251799813685248), (67887053190081/2251799813685248)), (515987396777105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1030801076442805/1125899906842624), (64989016278021/1125899906842624)), (2137067/1125899906842624), by norm_num⟩
  | 2 => ⟨((469991728628321/562949953421312), (118999473273261/1125899906842624)), (519979/140737488355328), by norm_num⟩
  | 3 => ⟨((1544378891929973/2251799813685248), (99349449821701/562949953421312)), (978149/140737488355328), by norm_num⟩
  | 4 => ⟨((123633389690395/281474976710656), (545104204368453/2251799813685248)), (1686959/140737488355328), by norm_num⟩
  | 5 => ⟨((151237948685747/1125899906842624), (957713276087555/4503599627370496)), (4597361/281474976710656), by norm_num⟩
  | 6 => ⟨((-489606617676581/18014398509481984), (1029168510801443/18014398509481984)), (25523177/2251799813685248), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-11001517/262144)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-1432725477/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((307521021800855/18014398509481984), (260435997350073/4503599627370496)), (159938807/18014398509481984), by norm_num⟩
  | 1 => ⟨((-219643271/4294967296), (-1488106771/8589934592)), (231/8589934592), by norm_num⟩
  | 2 => ⟨((164498109/2147483648), (557246185/2147483648)), (175/4294967296), by norm_num⟩
  | 3 => ⟨((-82132049/1073741824), (-1112906921/4294967296)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((123022815/2147483648), (833492795/4294967296)), (67/2147483648), by norm_num⟩
  | 5 => ⟨((-147417367/4294967296), (-499384253/4294967296)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((294415309/17179869184), (997347683/17179869184)), (41/4294967296), by norm_num⟩
  | 7 => ⟨((-31499623/4294967296), (-426826663/17179869184)), (71/17179869184), by norm_num⟩
  | 8 => ⟨((377457749/137438953472), (639329205/68719476736)), (215/137438953472), by norm_num⟩
  | 9 => ⟨((-251280525/274877906944), (-851226281/274877906944)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((301107671/1099511627776), (1020018417/1099511627776)), (11/68719476736), by norm_num⟩
  | 11 => ⟨((-328013807/4398046511104), (-1111164397/4398046511104)), (97/2199023255552), by norm_num⟩
  | 12 => ⟨((327547183/17592186044416), (554791841/8796093022208)), (49/4398046511104), by norm_num⟩
  | 13 => ⟨((-37740141/8796093022208), (-1022774045/70368744177664)), (183/70368744177664), by norm_num⟩
  | 14 => ⟨((258421391/281474976710656), (875416347/281474976710656)), (79/140737488355328), by norm_num⟩
  | 15 => ⟨((-412886027/2251799813685248), (-699336801/1125899906842624)), (127/1125899906842624), by norm_num⟩
  | 16 => ⟨((309223999/9007199254740992), (1047512913/9007199254740992)), (3/140737488355328), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (1672228477107/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888818172449387/316912650057057350374175801344), (988299279357/316912650057057350374175801344)), (92395/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888468077700629/39614081257132168796771975168), (1111567594917/19807040628566084398385987584)), (103957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888163793224827/2475880078570760549798248448), (2361404627991/2475880078570760549798248448)), (110469/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769830327302575/154742504910672534362390528), (36885061403/2417851639229258349412352)), (55243/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774139195049761/4835703278458516698824704), (276536970659/1208925819614629174706176)), (51799/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257673330006145/604462909807314587353088), (967475619555/302231454903657293676544)), (45333/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885980161951555/75557863725914323419136), (1571391184421/37778931862957161709568)), (147363/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648090518167043/2361183241434822606848), (2355763327693/4722366482869645213696)), (110551/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809790547717909/295147905179352825856), (3237025416591/590295810358705651712)), (76027/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821142049464793/73786976294838206464), (1010765140039/18446744073709551616)), (190137/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820034396168663/9223372036854775808), (2272009035043/4611686018427387904)), (13375/576460752303423488), by norm_num⟩
  | 6 => ⟨((397821237295927/288230376151711744), (4538492895781/1152921504606846976)), (26765/144115188075855872), by norm_num⟩
  | 5 => ⟨((298054941713291/36028797018963968), (3964973910513/144115188075855872)), (93745/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488100508326783/36028797018963968), (5935067210019/36028797018963968)), (140753/18014398509481984), by norm_num⟩
  | 3 => ⟨((92802788147993/562949953421312), (231162265333/281474976710656)), (176179/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219146057700029/4503599627370496), (7364824762797/2251799813685248)), (706145/4503599627370496), by norm_num⟩
  | 1 => ⟨((550740229400069/562949953421312), (21933295768889/2251799813685248)), (531403/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154687775652717/2251799813685248), (10806456023077/562949953421312)), (2140053/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2154687775652717/2251799813685248), (10806456023077/562949953421312)), (8163654335982512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060934062821393/2251799813685248), (41361649556131/1125899906842624)), (4177683/2251799813685248), by norm_num⟩
  | 2 => ⟨((1883207397615595/2251799813685248), (37855777386003/562949953421312)), (7954101/2251799813685248), by norm_num⟩
  | 3 => ⟨((782383301329875/1125899906842624), (126636976488843/1125899906842624)), (14373975/2251799813685248), by norm_num⟩
  | 4 => ⟨((529431348881813/1125899906842624), (351998095509653/2251799813685248)), (23210297/2251799813685248), by norm_num⟩
  | 5 => ⟨((27680290100941/140737488355328), (662079552105527/4503599627370496)), (58169467/4503599627370496), by norm_num⟩
  | 6 => ⟨((307521021800855/18014398509481984), (260435997350073/4503599627370496)), (159938807/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1432725477/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-728029821/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((431580220456167/9007199254740992), (71982363667647/2251799813685248)), (52701091/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1253085771/8589934592), (-835998235/8589934592)), (155/8589934592), by norm_num⟩
  | 2 => ⟨((953761937/4294967296), (318151923/2147483648)), (15/536870912), by norm_num⟩
  | 3 => ⟨((-967916539/4294967296), (-80718389/536870912)), (31/1073741824), by norm_num⟩
  | 4 => ⟨((736710905/4294967296), (491497893/4294967296)), (3/134217728), by norm_num⟩
  | 5 => ⟨((-28036661/268435456), (-598550545/8589934592)), (119/8589934592), by norm_num⟩
  | 6 => ⟨((910487931/17179869184), (303716761/8589934592)), (123/17179869184), by norm_num⟩
  | 7 => ⟨((-792000267/34359738368), (-264192141/17179869184)), (109/34359738368), by norm_num⟩
  | 8 => ⟨((301407823/34359738368), (804338901/137438953472)), (21/17179869184), by norm_num⟩
  | 9 => ⟨((-796565/268435456), (-544183963/274877906944)), (115/274877906944), by norm_num⟩
  | 10 => ⟨((993345543/1099511627776), (331356057/549755813888)), (71/549755813888), by norm_num⟩
  | 11 => ⟨((-1099731925/4398046511104), (-183421991/1099511627776)), (159/4398046511104), by norm_num⟩
  | 12 => ⟨((1116052841/17592186044416), (372288245/8796093022208)), (41/4398046511104), by norm_num⟩
  | 13 => ⟨((-1045491667/70368744177664), (-348750743/35184372088832)), (39/17592186044416), by norm_num⟩
  | 14 => ⟨((909435097/281474976710656), (606731121/281474976710656)), (69/140737488355328), by norm_num⟩
  | 15 => ⟨((-369172741/562949953421312), (-492588403/1125899906842624)), (57/562949953421312), by norm_num⟩
  | 16 => ⟨((561977347/4503599627370496), (749848223/9007199254740992)), (11/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (766376302779/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777567576289011/633825300114114700748351602688), (905799551467/633825300114114700748351602688)), (46145/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944195411089783/19807040628566084398385987584), (63673442859/2475880078570760549798248448)), (12979/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888081854810337/2475880078570760549798248448), (1082133580873/2475880078570760549798248448)), (13791/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442437138118397/38685626227668133590597632), (1081779462055/154742504910672534362390528)), (431/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((48381309370951/302231454903657293676544), (253448039035/2417851639229258349412352)), (12931/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257606574575011/604462909807314587353088), (886692229119/604462909807314587353088)), (90525/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942936004699097/37778931862957161709568), (1440170432349/75557863725914323419136)), (73559/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162012525748415/590295810358705651712), (1079511825643/4722366482869645213696)), (110351/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809735207354465/295147905179352825856), (370832121599/147573952589676412928)), (75877/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821004388988051/73786976294838206464), (231582682871/9223372036854775808)), (189725/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819880475742967/9223372036854775808), (260273109543/1152921504606846976)), (213485/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397783052668903/288230376151711744), (2079613868435/1152921504606846976)), (213541/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192087446753399/144115188075855872), (14193546711/1125899906842624)), (186911/144115188075855872), by norm_num⟩
  | 4 => ⟨((743952335740175/18014398509481984), (84981100319/1125899906842624)), (70123/9007199254740992), by norm_num⟩
  | 3 => ⟨((46393888129697/281474976710656), (1694588817679/4503599627370496)), (87709/2251799813685248), by norm_num⟩
  | 2 => ⟨((2218679415296355/4503599627370496), (3374125354683/2251799813685248)), (702337/4503599627370496), by norm_num⟩
  | 1 => ⟨((275286877759237/281474976710656), (10047444636645/2251799813685248)), (527593/1125899906842624), by norm_num⟩
  | 0 => ⟨((2153490604603241/2251799813685248), (19797135267433/2251799813685248)), (529291/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2153490604603241/2251799813685248), (19797135267433/2251799813685248)), (2019084932567405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2059299334411351/2251799813685248), (37865661536497/2251799813685248)), (4086693/2251799813685248), by norm_num⟩
  | 2 => ⟨((1882618479058101/2251799813685248), (69257250245117/2251799813685248)), (7612107/2251799813685248), by norm_num⟩
  | 3 => ⟨((392958529158385/562949953421312), (115805124707621/2251799813685248)), (1649557/281474976710656), by norm_num⟩
  | 4 => ⟨((1091238949559689/2251799813685248), (161671961059931/2251799813685248)), (19780495/2251799813685248), by norm_num⟩
  | 5 => ⟨((517214991743473/2251799813685248), (313389742530557/4503599627370496)), (11005951/1125899906842624), by norm_num⟩
  | 6 => ⟨((431580220456167/9007199254740992), (71982363667647/2251799813685248)), (52701091/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-728029821/16777216)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile000Terms2

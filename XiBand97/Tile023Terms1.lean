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
namespace Reinmann.XiBand97.Tile023Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28967/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28967/1280))
  have he : value ((69/80), (28967/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1668468031/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((580145401160253/4503599627370496), (348750967947195/4503599627370496)), (16389501/1125899906842624), by norm_num⟩
  | 1 => ⟨((-607828967/2147483648), (-730785559/4294967296)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((1335536745/4294967296), (200712499/1073741824)), (157/4294967296), by norm_num⟩
  | 3 => ⟨((-489079027/2147483648), (-588013915/4294967296)), (59/2147483648), by norm_num⟩
  | 4 => ⟨((1074616459/8589934592), (645999313/8589934592)), (33/2147483648), by norm_num⟩
  | 5 => ⟨((-472234739/8589934592), (-567762227/17179869184)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((691737183/34359738368), (415833707/34359738368)), (89/34359738368), by norm_num⟩
  | 7 => ⟨((-434257697/68719476736), (-522102881/137438953472)), (57/68719476736), by norm_num⟩
  | 8 => ⟨((954161685/549755813888), (573588641/549755813888)), (127/549755813888), by norm_num⟩
  | 9 => ⟨((-465890557/1099511627776), (-560134693/2199023255552)), (63/1099511627776), by norm_num⟩
  | 10 => ⟨((409466473/4398046511104), (246148343/4398046511104)), (113/8796093022208), by norm_num⟩
  | 11 => ⟨((-1308639707/70368744177664), (-393340501/35184372088832)), (183/70368744177664), by norm_num⟩
  | 12 => ⟨((958458443/281474976710656), (576171611/281474976710656)), (17/35184372088832), by norm_num⟩
  | 13 => ⟨((-323992069/562949953421312), (-389531823/1125899906842624)), (187/2251799813685248), by norm_num⟩
  | 14 => ⟨((813580957/9007199254740992), (489079369/9007199254740992)), (15/1125899906842624), by norm_num⟩
  | 15 => ⟨((-953397373/72057594037927936), (-573129179/72057594037927936)), (143/72057594037927936), by norm_num⟩
  | 16 => ⟨((523707035/288230376151711744), (629646759/576460752303423488)), (159/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (352525989001/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779045486360211/633825300114114700748351602688), (52164972443/39614081257132168796771975168)), (92283/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890053131889493/39614081257132168796771975168), (469406723729/19807040628566084398385987584)), (103823/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944923818062871/1237940039285380274899124224), (997296466389/2475880078570760549798248448)), (55159/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885756929194803/77371252455336267181195264), (124634951581/19342813113834066795298816)), (110325/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774928184614055/4835703278458516698824704), (934531794727/9671406556917033397649408)), (103437/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259053730519351/604462909807314587353088), (817485051355/604462909807314587353088)), (90515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888222691827557/75557863725914323419136), (331995402325/18889465931478580854784)), (36775/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297862390490589/4722366482869645213696), (995608712933/4722366482869645213696)), (110337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621892074783605/590295810358705651712), (1368348843361/590295810358705651712)), (151733/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824029450011951/73786976294838206464), (106844803601/4611686018427387904)), (741/288230376151711744), by norm_num⟩
  | 7 => ⟨((1823280902252141/9223372036854775808), (240242924475/1152921504606846976)), (213447/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797264590778867/576460752303423488), (240045724759/144115188075855872)), (106749/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195055913229609/144115188075855872), (1678546977425/144115188075855872)), (46717/36028797018963968), by norm_num⟩
  | 4 => ⟨((373087404106665/9007199254740992), (78571203873/1125899906842624)), (8763/1125899906842624), by norm_num⟩
  | 3 => ⟨((1490147055929037/9007199254740992), (392082413217/1125899906842624)), (685/17592186044416), by norm_num⟩
  | 2 => ⟨((278715519026659/562949953421312), (6254790203341/4503599627370496)), (702041/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218761145507303/2251799813685248), (583499844149/140737488355328)), (1054573/2251799813685248), by norm_num⟩
  | 0 => ⟨((1093010522467321/1125899906842624), (18488041022221/2251799813685248)), (264403/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1093010522467321/1125899906842624), (18488041022221/2251799813685248)), (1008617402196788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2122011988897079/2251799813685248), (35895949993927/2251799813685248)), (1035401/562949953421312), by norm_num⟩
  | 2 => ⟨((999566287917413/1125899906842624), (67654003501583/2251799813685248)), (7937829/2251799813685248), by norm_num⟩
  | 3 => ⟨((1772783693875987/2251799813685248), (120125529333189/2251799813685248)), (14571277/2251799813685248), by norm_num⟩
  | 4 => ⟨((694629216918543/1125899906842624), (189143438351723/2251799813685248)), (24497831/2251799813685248), by norm_num⟩
  | 5 => ⟨((841222094523513/2251799813685248), (466771718050787/4503599627370496)), (34343571/2251799813685248), by norm_num⟩
  | 6 => ⟨((580145401160253/4503599627370496), (348750967947195/4503599627370496)), (16389501/1125899906842624), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1668468031/33554432)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-437118451/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-41559375777725/1125899906842624), (-595327232309957/4503599627370496)), (106241373/4503599627370496), by norm_num⟩
  | 1 => ⟨((365043637/4294967296), (81705547/268435456)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((-210136009/2147483648), (-376267949/1073741824)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((322570695/4294967296), (577592647/2147483648)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-371373237/8589934592), (-1329956219/8589934592)), (247/8589934592), by norm_num⟩
  | 5 => ⟨((10688981/536870912), (612467473/8589934592)), (115/8589934592), by norm_num⟩
  | 6 => ⟨((-262531075/34359738368), (-235043079/8589934592)), (179/34359738368), by norm_num⟩
  | 7 => ⟨((345428651/137438953472), (1237043863/137438953472)), (119/68719476736), by norm_num⟩
  | 8 => ⟨((-397689431/549755813888), (-1424199379/549755813888)), (277/549755813888), by norm_num⟩
  | 9 => ⟨((406983891/2199023255552), (91092785/137438953472)), (143/1099511627776), by norm_num⟩
  | 10 => ⟨((-5856969/137438953472), (-1342392889/8796093022208)), (133/4398046511104), by norm_num⟩
  | 11 => ⟨((313859945/35184372088832), (1123990493/35184372088832)), (7/1099511627776), by norm_num⟩
  | 12 => ⟨((-120448205/70368744177664), (-862694585/140737488355328)), (87/70368744177664), by norm_num⟩
  | 13 => ⟨((341344297/1125899906842624), (1222417041/1125899906842624)), (31/140737488355328), by norm_num⟩
  | 14 => ⟨((-224564083/4503599627370496), (-402102751/2251799813685248)), (329/9007199254740992), by norm_num⟩
  | 15 => ⟨((275774885/36028797018963968), (493800427/18014398509481984)), (51/9007199254740992), by norm_num⟩
  | 16 => ⟨((-158748785/144115188075855872), (-568508751/144115188075855872)), (237/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-2400840323303/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778901418690369/633825300114114700748351602688), (-710421336207/158456325028528675187087900672)), (1445/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((472472714702925/9903520314283042199192993792), (-399541661619/4951760157141521099596496896)), (52029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889674963870479/2475880078570760549798248448), (-3395415363247/2475880078570760549798248448)), (55291/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442835224281029/38685626227668133590597632), (-1697320333785/77371252455336267181195264)), (55303/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549693911168745/9671406556917033397649408), (-3181652690721/9671406556917033397649408)), (51859/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629455636534963/302231454903657293676544), (-1391561685279/302231454903657293676544)), (45389/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943995311993561/37778931862957161709568), (-2260516639485/37778931862957161709568)), (147561/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297687837414407/4722366482869645213696), (-847356490877/1180591620717411303424)), (110711/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621651249132409/590295810358705651712), (-4658269383621/590295810358705651712)), (76147/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113982949797439/4611686018427387904), (-5819551158277/73786976294838206464)), (190467/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911469595376973/4611686018427387904), (-408904979515/576460752303423488)), (214413/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99636586133687/72057594037927936), (-6536838865129/1152921504606846976)), (26823/144115188075855872), by norm_num⟩
  | 5 => ⟨((298688184266799/36028797018963968), (-2856696399547/72057594037927936)), (93977/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491890168920875/36028797018963968), (-8557418530395/36028797018963968)), (141159/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489564580215113/9007199254740992), (-5337312959007/4503599627370496)), (176787/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114267409518027/2251799813685248), (-21282915761091/4503599627370496)), (709181/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216916600547809/2251799813685248), (-15879451546549/1125899906842624)), (1068869/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091046109947441/1125899906842624), (-31429070222129/1125899906842624)), (2158193/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091046109947441/1125899906842624), (-31429070222129/1125899906842624)), (8232852944380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112787860355809/2251799813685248), (-121824558636941/2251799813685248)), (2151629/1125899906842624), by norm_num⟩
  | 2 => ⟨((1975766803399189/2251799813685248), (-228607753688455/2251799813685248)), (4270413/1125899906842624), by norm_num⟩
  | 3 => ⟨((1710362054815459/2251799813685248), (-401168530161751/2251799813685248)), (16721895/2251799813685248), by norm_num⟩
  | 4 => ⟨((153455146865179/281474976710656), (-304708894371841/1125899906842624)), (31360509/2251799813685248), by norm_num⟩
  | 5 => ⟨((504357805797377/2251799813685248), (-664487460780907/2251799813685248)), (51168941/2251799813685248), by norm_num⟩
  | 6 => ⟨((-41559375777725/1125899906842624), (-595327232309957/4503599627370496)), (106241373/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-437118451/8388608)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-910423915/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-744258455578737/9007199254740992), (861738471208407/9007199254740992)), (206723033/9007199254740992), by norm_num⟩
  | 1 => ⟨((425494631/2147483648), (-492658283/2147483648)), (239/4294967296), by norm_num⟩
  | 2 => ⟨((-255072891/1073741824), (147667871/536870912)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((815517439/4294967296), (-944245573/4294967296)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((-488881353/4294967296), (566050499/4294967296)), (283/8589934592), by norm_num⟩
  | 5 => ⟨((234457257/4294967296), (-1085863853/17179869184)), (137/8589934592), by norm_num⟩
  | 6 => ⟨((-46850329/2147483648), (867929267/34359738368)), (221/34359738368), by norm_num⟩
  | 7 => ⟨((513564263/68719476736), (-9291087/1073741824)), (77/34359738368), by norm_num⟩
  | 8 => ⟨((-615736659/274877906944), (712929715/274877906944)), (187/274877906944), by norm_num⟩
  | 9 => ⟨((164052447/274877906944), (-94973933/137438953472)), (101/549755813888), by norm_num⟩
  | 10 => ⟨((-629408939/4398046511104), (45547509/274877906944)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((548820625/17592186044416), (-158862773/4398046511104)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((-438671461/70368744177664), (1015830113/140737488355328)), (279/140737488355328), by norm_num⟩
  | 13 => ⟨((647315829/562949953421312), (-93686701/70368744177664)), (13/35184372088832), by norm_num⟩
  | 14 => ⟨((-886968895/4503599627370496), (1026975531/4503599627370496)), (287/4503599627370496), by norm_num⟩
  | 15 => ⟨((17723821/562949953421312), (-656687939/18014398509481984)), (185/18014398509481984), by norm_num⟩
  | 16 => ⟨((-679997865/144115188075855872), (196833613/36028797018963968)), (7/4503599627370496), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (2974088682787/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778772373744487/633825300114114700748351602688), (879929177003/158456325028528675187087900672)), (92547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118109098696947/2475880078570760549798248448), (1979476028499/19807040628566084398385987584)), (104137/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944760232967555/1237940039285380274899124224), (2102748824373/1237940039285380274899124224)), (6917/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885593121876601/77371252455336267181195264), (2102248885705/77371252455336267181195264)), (27675/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774774379305027/4835703278458516698824704), (3940654492249/9671406556917033397649408)), (103813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258784099700231/604462909807314587353088), (861752684601/151115727451828646838272)), (90867/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471945914603177/18889465931478580854784), (2799700894337/37778931862957161709568)), (36929/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324383085823443/1180591620717411303424), (4197809993613/4722366482869645213696)), (55419/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405359251657907/147573952589676412928), (2884579976175/295147905179352825856)), (38121/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911729368748885/36893488147419103232), (7207208335021/73786976294838206464)), (23841/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822636273509843/9223372036854775808), (8102279734149/9223372036854775808)), (214739/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593881337589805/1152921504606846976), (8094996528857/1152921504606846976)), (26869/144115188075855872), by norm_num⟩
  | 5 => ⟨((597242720591903/72057594037927936), (7074933649777/144115188075855872)), (94161/72057594037927936), by norm_num⟩
  | 4 => ⟨((186435839070905/4503599627370496), (2649009271619/9007199254740992)), (141481/18014398509481984), by norm_num⟩
  | 3 => ⟨((372263970360181/2251799813685248), (6608220114107/4503599627370496)), (177271/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113752180352955/2251799813685248), (13173590668241/2251799813685248)), (177901/1125899906842624), by norm_num⟩
  | 1 => ⟨((69229328754929/70368744177664), (9826735492281/562949953421312)), (268431/562949953421312), by norm_num⟩
  | 0 => ⟨((136175502269977/140737488355328), (38880536455927/1125899906842624)), (1086403/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((136175502269977/140737488355328), (38880536455927/1125899906842624)), (4144298557761764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052748482759515/1125899906842624), (37620229281373/562949953421312)), (2177409/1125899906842624), by norm_num⟩
  | 2 => ⟨((979321727132757/1125899906842624), (17587992971815/140737488355328)), (8725797/2251799813685248), by norm_num⟩
  | 3 => ⟨((1668484808875417/2251799813685248), (244772076796901/1125899906842624)), (542517/70368744177664), by norm_num⟩
  | 4 => ⟨((1129846473770863/2251799813685248), (90682681757607/281474976710656)), (8318803/562949953421312), by norm_num⟩
  | 5 => ⟨((666363615810505/4503599627370496), (1456008763738021/4503599627370496)), (54832375/2251799813685248), by norm_num⟩
  | 6 => ⟨((-744258455578737/9007199254740992), (861738471208407/9007199254740992)), (206723033/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-910423915/16777216)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-943460069/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1004651646280463/9007199254740992), (163163477746293/4503599627370496)), (10810535/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1190407541/4294967296), (-386663447/4294967296)), (105/4294967296), by norm_num⟩
  | 2 => ⟨((1479025807/4294967296), (480411285/4294967296)), (133/4294967296), by norm_num⟩
  | 3 => ⟨((-612540177/2147483648), (-99481433/1073741824)), (7/268435456), by norm_num⟩
  | 4 => ⟨((1522105159/8589934592), (494404149/8589934592)), (71/4294967296), by norm_num⟩
  | 5 => ⟨((-378228923/4294967296), (-491419263/17179869184)), (143/17179869184), by norm_num⟩
  | 6 => ⟨((1253151421/34359738368), (407043665/34359738368)), (121/34359738368), by norm_num⟩
  | 7 => ⟨((-889704085/68719476736), (-144495073/34359738368)), (11/8589934592), by norm_num⟩
  | 8 => ⟨((552707899/137438953472), (2805131/2147483648)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((-610412237/549755813888), (-99135839/274877906944)), (63/549755813888), by norm_num⟩
  | 10 => ⟨((1213453941/4398046511104), (394149289/4398046511104)), (127/4398046511104), by norm_num⟩
  | 11 => ⟨((-1096479915/17592186044416), (-356154251/17592186044416)), (117/17592186044416), by norm_num⟩
  | 12 => ⟨((113527093/8796093022208), (295003355/70368744177664)), (99/70368744177664), by norm_num⟩
  | 13 => ⟨((-86801301/35184372088832), (-451111261/562949953421312)), (77/281474976710656), by norm_num⟩
  | 14 => ⟨((986025737/2251799813685248), (320276963/2251799813685248)), (111/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1306763685/18014398509481984), (-424457789/18014398509481984)), (75/9007199254740992), by norm_num⟩
  | 16 => ⟨((405898221/36028797018963968), (16480281/4503599627370496)), (95/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (204552684531/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778663194492331/633825300114114700748351602688), (60512513837/79228162514264337593543950336)), (11531/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944811571798641/19807040628566084398385987584), (544510930299/39614081257132168796771975168)), (51891/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472347721474209/618970019642690137449562112), (289208207639/1237940039285380274899124224)), (1723/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((110691077155053/9671406556917033397649408), (578274216597/154742504910672534362390528)), (27569/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774714209241131/4835703278458516698824704), (541981041109/9671406556917033397649408)), (103389/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629339703866485/302231454903657293676544), (474082429325/604462909807314587353088)), (90469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887614668656379/75557863725914323419136), (385050487271/37778931862957161709568)), (36755/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648703296469057/2361183241434822606848), (577328246851/4722366482869645213696)), (110273/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621265710157679/590295810358705651712), (99178049733/73786976294838206464)), (37909/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455811757344553/18446744073709551616), (991177969815/73786976294838206464)), (189561/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911200707138427/4611686018427387904), (1114247365589/9223372036854775808)), (6665/288230376151711744), by norm_num⟩
  | 6 => ⟨((1593650611742681/1152921504606846976), (139151686131/144115188075855872)), (106655/576460752303423488), by norm_num⟩
  | 5 => ⟨((597144098176759/72057594037927936), (972899978247/144115188075855872)), (23335/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491200101494969/36028797018963968), (1457029530271/36028797018963968)), (140043/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488713761100089/9007199254740992), (1817233364873/9007199254740992)), (175113/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226868331779101/4503599627370496), (3622334900839/4503599627370496)), (700807/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214504242653825/2251799813685248), (5403273394097/2251799813685248)), (263027/562949953421312), by norm_num⟩
  | 0 => ⟨((272201747585595/281474976710656), (166972386807/35184372088832)), (2107847/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((272201747585595/281474976710656), (166972386807/35184372088832)), (8040798195845793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1052910748212281/1125899906842624), (10334173450111/1125899906842624)), (4096815/2251799813685248), by norm_num⟩
  | 2 => ⟨((1969116867002271/2251799813685248), (9664235899997/562949953421312)), (7737665/2251799813685248), by norm_num⟩
  | 3 => ⟨((1721257304076727/2251799813685248), (8451022067645/281474976710656)), (1724785/281474976710656), by norm_num⟩
  | 4 => ⟨((1313685090177269/2251799813685248), (103358270996861/2251799813685248)), (10961573/1125899906842624), by norm_num⟩
  | 5 => ⟨((1523302003621473/4503599627370496), (120597060830965/2251799813685248)), (55184389/4503599627370496), by norm_num⟩
  | 6 => ⟨((1004651646280463/9007199254740992), (163163477746293/4503599627370496)), (10810535/1125899906842624), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-943460069/16777216)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1947700771/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((144707448099707/18014398509481984), (-122899706523699/1125899906842624)), (77671387/4503599627370496), by norm_num⟩
  | 1 => ⟨((-88493175/4294967296), (601256415/2147483648)), (3/67108864), by norm_num⟩
  | 2 => ⟨((7093141/268435456), (-12048377/33554432)), (249/4294967296), by norm_num⟩
  | 3 => ⟨((-97032253/4294967296), (659274173/2147483648)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((1944397/134217728), (-1691004867/8589934592)), (139/4294967296), by norm_num⟩
  | 5 => ⟨((-31918591/4294967296), (1734936739/17179869184)), (287/17179869184), by norm_num⟩
  | 6 => ⟨((54579713/17179869184), (-1483341625/34359738368)), (247/34359738368), by norm_num⟩
  | 7 => ⟨((-39998343/34359738368), (543528021/34359738368)), (183/68719476736), by norm_num⟩
  | 8 => ⟨((25648431/68719476736), (-174265231/34359738368)), (237/274877906944), by norm_num⟩
  | 9 => ⟨((-14619317/137438953472), (198658441/137438953472)), (273/1099511627776), by norm_num⟩
  | 10 => ⟨((119992985/4398046511104), (-815278145/2199023255552)), (141/2199023255552), by norm_num⟩
  | 11 => ⟨((-13989815/2199023255552), (760417147/8796093022208)), (265/17592186044416), by norm_num⟩
  | 12 => ⟨((95688445/70368744177664), (-1300287649/70368744177664)), (229/70368744177664), by norm_num⟩
  | 13 => ⟨((-37759387/140737488355328), (128275845/35184372088832)), (91/140737488355328), by norm_num⟩
  | 14 => ⟨((110686761/2251799813685248), (-1504096211/2251799813685248)), (269/2251799813685248), by norm_num⟩
  | 15 => ⟨((-37854125/4503599627370496), (128597687/1125899906842624)), (93/4503599627370496), by norm_num⟩
  | 16 => ⟨((48546957/36028797018963968), (-1319386219/72057594037927936)), (241/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-1950450610769/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111159628793927/39614081257132168796771975168), (-2307732520035/633825300114114700748351602688)), (23107/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889500238057007/39614081257132168796771975168), (-1297847750777/19807040628566084398385987584)), (25999/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472315031694925/618970019642690137449562112), (-2757303835833/2475880078570760549798248448)), (6907/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770926282077305/154742504910672534362390528), (-2756603592721/154742504910672534362390528)), (27633/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48415795168383/302231454903657293676544), (-322946509191/1208925819614629174706176)), (25911/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258571601230143/604462909807314587353088), (-564970502505/151115727451828646838272)), (22677/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887439098990091/75557863725914323419136), (-917728653123/18889465931478580854784)), (73719/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648637289981299/2361183241434822606848), (-2751967022689/4722366482869645213696)), (27653/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202635455929779/73786976294838206464), (-1890987420357/295147905179352825856)), (152145/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823018634844183/73786976294838206464), (-4724500501049/73786976294838206464)), (190263/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455535837540061/2305843009213693952), (-663873089133/1152921504606846976)), (214157/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593391150169297/1152921504606846976), (-5305890849351/1152921504606846976)), (26787/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194059599285909/144115188075855872), (-4636929495253/144115188075855872)), (93833/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490854079364135/36028797018963968), (-3471979116293/18014398509481984)), (281813/36028797018963968), by norm_num⟩
  | 3 => ⟨((372068946032429/2251799813685248), (-1082495776145/1125899906842624)), (176409/4503599627370496), by norm_num⟩
  | 2 => ⟨((69561753692373/140737488355328), (-17260113264045/4503599627370496)), (707291/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213125580766159/2251799813685248), (-12870530439137/1125899906842624)), (1065087/2251799813685248), by norm_num⟩
  | 0 => ⟨((67959285281205/70368744177664), (-25444156653407/1125899906842624)), (2146843/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((67959285281205/70368744177664), (-25444156653407/1125899906842624)), (8189556130416106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099084454007357/2251799813685248), (-24572936762703/562949953421312)), (2121851/1125899906842624), by norm_num⟩
  | 2 => ⟨((1952435669812875/2251799813685248), (-91625675132249/1125899906842624)), (4141137/1125899906842624), by norm_num⟩
  | 3 => ⟨((838978661517917/1125899906842624), (-317778223999613/2251799813685248)), (15710407/2251799813685248), by norm_num⟩
  | 4 => ⟨((1205505818849255/2251799813685248), (-473592985327429/2251799813685248)), (27847785/2251799813685248), by norm_num⟩
  | 5 => ⟨((1091530389210563/4503599627370496), (-1014156047280333/4503599627370496)), (83060995/4503599627370496), by norm_num⟩
  | 6 => ⟨((144707448099707/18014398509481984), (-122899706523699/1125899906842624)), (77671387/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1947700771/33554432)), (1/16777216), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1001987423/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1848630234627993/18014398509481984), (60738251389501/18014398509481984)), (301839245/18014398509481984), by norm_num⟩
  | 1 => ⟨((1163158695/4294967296), (-19108263/2147483648)), (3/67108864), by norm_num⟩
  | 2 => ⟨((-1534821239/4294967296), (25213901/2147483648)), (1/16777216), by norm_num⟩
  | 3 => ⟨((1350160413/4294967296), (-11090155/1073741824)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-1781575367/8589934592), (29267555/4294967296)), (151/4294967296), by norm_num⟩
  | 5 => ⟨((470167953/4294967296), (-15447751/4294967296)), (321/17179869184), by norm_num⟩
  | 6 => ⟨((-1654400243/34359738368), (54356667/34359738368)), (71/8589934592), by norm_num⟩
  | 7 => ⟨((623722441/34359738368), (-40985817/68719476736)), (27/8589934592), by norm_num⟩
  | 8 => ⟨((-1646039279/274877906944), (6760245/34359738368)), (287/274877906944), by norm_num⟩
  | 9 => ⟨((1930663121/1099511627776), (-15858377/274877906944)), (339/1099511627776), by norm_num⟩
  | 10 => ⟨((-254756533/549755813888), (33480933/2199023255552)), (361/4398046511104), by norm_num⟩
  | 11 => ⟨((1955831551/17592186044416), (-32130219/8796093022208)), (349/17592186044416), by norm_num⟩
  | 12 => ⟨((-430129299/17592186044416), (56528993/70368744177664)), (309/70368744177664), by norm_num⟩
  | 13 => ⟨((1397090313/281474976710656), (-45902539/281474976710656)), (253/281474976710656), by norm_num⟩
  | 14 => ⟨((-263357245/281474976710656), (17305633/562949953421312)), (3/17592186044416), by norm_num⟩
  | 15 => ⟨((92668649/562949953421312), (-48715261/9007199254740992)), (17/562949953421312), by norm_num⟩
  | 16 => ⟨((-978231509/36028797018963968), (64281183/72057594037927936)), (181/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (506186527005/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889223056034597/316912650057057350374175801344), (2395384634809/316912650057057350374175801344)), (181/1237940039285380274899124224), by norm_num⟩
  | 16 => ⟨((1889378290840087/39614081257132168796771975168), (5388512960437/39614081257132168796771975168)), (52143/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472282472951287/618970019642690137449562112), (2861980935837/1237940039285380274899124224)), (110839/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770795298438671/154742504910672534362390528), (5722462111325/154742504910672534362390528)), (110879/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48411932917045/302231454903657293676544), (5363214949049/9671406556917033397649408)), (103991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629231331978213/302231454903657293676544), (4691220041289/604462909807314587353088)), (45517/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471815147024521/18889465931478580854784), (3810123065891/37778931862957161709568)), (148009/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297139396319225/4722366482869645213696), (2856285990791/2361183241434822606848)), (27769/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620895659225183/590295810358705651712), (7850541935965/590295810358705651712)), (152841/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455695122003217/18446744073709551616), (9806812301963/73786976294838206464)), (191219/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821871095114127/9223372036854775808), (11023914553501/9223372036854775808)), (215353/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593113481224037/1152921504606846976), (11012982080447/1152921504606846976)), (215643/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596905281665685/72057594037927936), (4812032993321/72057594037927936)), (94507/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490468411653753/36028797018963968), (14411526598097/36028797018963968)), (284173/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487772584573127/9007199254740992), (17971438830427/9007199254740992)), (356361/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112453355211677/2251799813685248), (17907049476711/2251799813685248)), (5595/35184372088832), by norm_num⟩
  | 1 => ⟨((552841280304687/562949953421312), (26699828741949/1125899906842624)), (541431/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085278918337969/1125899906842624), (13189513167981/281474976710656)), (550085/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085278918337969/1125899906842624), (13189513167981/281474976710656)), (2098407747508811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1043651315117609/1125899906842624), (50854611488485/562949953421312)), (2224061/1125899906842624), by norm_num⟩
  | 2 => ⟨((239555775551489/281474976710656), (94279219382103/562949953421312)), (4525007/1125899906842624), by norm_num⟩
  | 3 => ⟨((783939339019223/1125899906842624), (320954022718477/1125899906842624)), (4608931/562949953421312), by norm_num⟩
  | 4 => ⟨((454347139966703/1125899906842624), (446946452160339/1125899906842624)), (18091759/1125899906842624), by norm_num⟩
  | 5 => ⟨((23697284125065/4503599627370496), (1442890907251487/4503599627370496)), (115861005/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1848630234627993/18014398509481984), (60738251389501/18014398509481984)), (301839245/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1001987423/16777216)), (1/16777216), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-2056364757/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((40757482646609/18014398509481984), (871148637316249/9007199254740992)), (69877477/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3289381/536870912), (-1124913331/4294967296)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((8907809/1073741824), (761580443/2147483648)), (249/4294967296), by norm_num⟩
  | 3 => ⟨((-32163725/4294967296), (-85933253/268435456)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((43550491/8589934592), (232711563/1073741824)), (309/8589934592), by norm_num⟩
  | 5 => ⟨((-23587383/8589934592), (-126038919/1073741824)), (337/17179869184), by norm_num⟩
  | 6 => ⟨((21291939/17179869184), (1820371839/34359738368)), (307/34359738368), by norm_num⟩
  | 7 => ⟨((-16474183/34359738368), (-1408473807/68719476736)), (15/4294967296), by norm_num⟩
  | 8 => ⟨((44612915/274877906944), (238388611/34359738368)), (327/274877906944), by norm_num⟩
  | 9 => ⟨((-26847559/549755813888), (-35864907/17179869184)), (199/549755813888), by norm_num⟩
  | 10 => ⟨((29081815/2199023255552), (621593399/1099511627776)), (217/2199023255552), by norm_num⟩
  | 11 => ⟨((-28638187/8796093022208), (-1224222639/8796093022208)), (27/1099511627776), by norm_num⟩
  | 12 => ⟨((1615701/2199023255552), (552542727/17592186044416)), (197/35184372088832), by norm_num⟩
  | 13 => ⟨((-5385107/35184372088832), (-1841616545/281474976710656)), (165/140737488355328), by norm_num⟩
  | 14 => ⟨((8333223/281474976710656), (356227861/281474976710656)), (257/1125899906842624), by norm_num⟩
  | 15 => ⟨((-48142477/9007199254740992), (-514497563/2251799813685248)), (187/4503599627370496), by norm_num⟩
  | 16 => ⟨((32593061/36028797018963968), (1393285229/36028797018963968)), (255/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (251958902017/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889181830763697/316912650057057350374175801344), (2384414276673/633825300114114700748351602688)), (92435/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889286071472013/39614081257132168796771975168), (2681918213611/39614081257132168796771975168)), (104005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944516306688367/1237940039285380274899124224), (2848858942429/2475880078570760549798248448)), (55261/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770698812098857/154742504910672534362390528), (2848095148157/154742504910672534362390528)), (55271/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549092238421615/9671406556917033397649408), (1334638958931/4835703278458516698824704)), (51827/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629192545636033/302231454903657293676544), (2334807173421/604462909807314587353088)), (45359/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29486501668993/1180591620717411303424), (3792541615301/75557863725914323419136)), (9/4611686018427387904), by norm_num⟩
  | 10 => ⟨((648523705762335/2361183241434822606848), (1421538383633/2361183241434822606848)), (110627/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810385706917669/295147905179352825856), (3907071317913/590295810358705651712)), (152167/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822628527336133/73786976294838206464), (4880602232969/73786976294838206464)), (47573/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910852366444739/4611686018427387904), (1371557476883/2305843009213693952)), (214195/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592952849984457/1152921504606846976), (685084391009/144115188075855872)), (107169/576460752303423488), by norm_num⟩
  | 5 => ⟨((596838221666547/72057594037927936), (4789348104007/144115188075855872)), (187709/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490280058818997/36028797018963968), (7171553110267/36028797018963968)), (8809/1125899906842624), by norm_num⟩
  | 3 => ⟨((1487559506789319/9007199254740992), (4471328507261/4503599627370496)), (176465/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112273654073965/2251799813685248), (17820106540685/4503599627370496)), (707571/4503599627370496), by norm_num⟩
  | 1 => ⟨((69093491440453/70368744177664), (26567649922023/2251799813685248)), (532825/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170466852046611/2251799813685248), (3280519140977/140737488355328)), (2148547/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170466852046611/2251799813685248), (3280519140977/140737488355328)), (8196056374556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1045424043675145/1125899906842624), (101184952725859/2251799813685248)), (4242051/2251799813685248), by norm_num⟩
  | 2 => ⟨((1936853934888841/2251799813685248), (5872035215723/70368744177664)), (1032365/281474976710656), by norm_num⟩
  | 3 => ⟨((1650277616062247/2251799813685248), (80811975872869/562949953421312)), (15585947/2251799813685248), by norm_num⟩
  | 4 => ⟨((1163037223401479/2251799813685248), (59224711753795/281474976710656)), (27319715/2251799813685248), by norm_num⟩
  | 5 => ⟨((1002017427386313/4503599627370496), (122356425995361/562949953421312)), (19858721/1125899906842624), by norm_num⟩
  | 6 => ⟨((40757482646609/18014398509481984), (871148637316249/9007199254740992)), (69877477/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-2056364757/33554432)), (1/16777216), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile023Terms1

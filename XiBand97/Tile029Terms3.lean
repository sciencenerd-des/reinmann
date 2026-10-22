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
namespace Reinmann.XiBand97.Tile029Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6223/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6223/256))
  have he : value ((69/80), (6223/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-315155369/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((605313168448737/9007199254740992), (80295565537995/4503599627370496)), (197624317/18014398509481984), by norm_num⟩
  | 1 => ⟨((-446092773/2147483648), (-118349553/2147483648)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((344722925/1073741824), (365823493/4294967296)), (115/2147483648), by norm_num⟩
  | 3 => ⟨((-710368797/2147483648), (-94231329/1073741824)), (239/4294967296), by norm_num⟩
  | 4 => ⟨((1097890055/4294967296), (145636519/2147483648)), (187/4294967296), by norm_num⟩
  | 5 => ⟨((-339362477/2147483648), (-180067465/4294967296)), (233/8589934592), by norm_num⟩
  | 6 => ⟨((699322549/8589934592), (371064119/17179869184)), (121/8589934592), by norm_num⟩
  | 7 => ⟨((-1235220393/34359738368), (-327707127/34359738368)), (215/34359738368), by norm_num⟩
  | 8 => ⟨((954529669/68719476736), (31654895/8589934592)), (21/8589934592), by norm_num⟩
  | 9 => ⟨((-655664829/137438953472), (-347899109/274877906944)), (233/274877906944), by norm_num⟩
  | 10 => ⟨((1621350257/1099511627776), (215074183/549755813888)), (145/549755813888), by norm_num⟩
  | 11 => ⟨((-911211359/2199023255552), (-120873351/1099511627776)), (165/2199023255552), by norm_num⟩
  | 12 => ⟨((234716083/2199023255552), (124541553/4398046511104)), (43/2199023255552), by norm_num⟩
  | 13 => ⟨((-55809029/2199023255552), (-7403139/1099511627776)), (165/35184372088832), by norm_num⟩
  | 14 => ⟨((197152089/35184372088832), (52304953/35184372088832)), (147/140737488355328), by norm_num⟩
  | 15 => ⟨((-1300065017/1125899906842624), (-344910571/1125899906842624)), (61/281474976710656), by norm_num⟩
  | 16 => ⟨((15697485/70368744177664), (33316663/562949953421312)), (95/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (168902106015/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888928875539287/316912650057057350374175801344), (399383528805/633825300114114700748351602688)), (184479/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944358605358667/19807040628566084398385987584), (449203381761/39614081257132168796771975168)), (25943/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888428571157199/2475880078570760549798248448), (477148876683/2475880078570760549798248448)), (110261/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770095188432001/154742504910672534362390528), (14906344419/4835703278458516698824704)), (13783/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548526785690309/9671406556917033397649408), (447035424253/9671406556917033397649408)), (206753/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4913635798049/2361183241434822606848), (391001158719/604462909807314587353088)), (45229/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943166828845449/37778931862957161709568), (158771678251/18889465931478580854784)), (294001/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324111575562135/1180591620717411303424), (119015321597/1180591620717411303424)), (220513/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619946069732525/590295810358705651712), (327086104663/295147905179352825856)), (37903/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821598616933299/73786976294838206464), (408548832475/36893488147419103232)), (379059/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820548513809047/9223372036854775808), (918386477143/9223372036854775808)), (426481/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591799663688299/1152921504606846976), (917327180287/1152921504606846976)), (426531/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192670810520739/144115188075855872), (801471219049/144115188075855872)), (373271/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488778403308965/36028797018963968), (599915404069/18014398509481984)), (140005/9007199254740992), by norm_num⟩
  | 3 => ⟨((742847144464585/4503599627370496), (1495639698133/9007199254740992)), (350113/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220852277553721/4503599627370496), (372358721297/562949953421312)), (700529/2251799813685248), by norm_num⟩
  | 1 => ⟨((551384292922627/562949953421312), (4437409046571/2251799813685248)), (2103125/2251799813685248), by norm_num⟩
  | 0 => ⟨((539976648832063/562949953421312), (8752003359665/2251799813685248)), (2106265/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539976648832063/562949953421312), (8752003359665/2251799813685248)), (8034763340476607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((517932352892511/562949953421312), (16789689442187/2251799813685248)), (4056995/1125899906842624), by norm_num⟩
  | 2 => ⟨((1905933571452321/2251799813685248), (3861765732583/281474976710656)), (7525635/1125899906842624), by norm_num⟩
  | 3 => ⟨((201595869540955/281474976710656), (52297856390837/2251799813685248)), (25891927/2251799813685248), by norm_num⟩
  | 4 => ⟨((576934542282191/1125899906842624), (37456373413529/1125899906842624)), (38290915/2251799813685248), by norm_num⟩
  | 5 => ⟨((588774338028961/2251799813685248), (153547401644155/4503599627370496)), (83579689/4503599627370496), by norm_num⟩
  | 6 => ⟨((605313168448737/9007199254740992), (80295565537995/4503599627370496)), (197624317/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-315155369/4194304)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1278750261/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((102657550059011/2251799813685248), (-882331722376693/18014398509481984)), (70706253/4503599627370496), by norm_num⟩
  | 1 => ⟨((-613941487/4294967296), (659595969/4294967296)), (213/4294967296), by norm_num⟩
  | 2 => ⟨((962504991/4294967296), (-1034079673/4294967296)), (21/268435456), by norm_num⟩
  | 3 => ⟨((-1005976277/4294967296), (1080783611/4294967296)), (353/4294967296), by norm_num⟩
  | 4 => ⟨((788558199/4294967296), (-423598845/2147483648)), (279/4294967296), by norm_num⟩
  | 5 => ⟨((-989007869/8589934592), (1062553383/8589934592)), (353/8589934592), by norm_num⟩
  | 6 => ⟨((1033676151/17179869184), (-1110543329/17179869184)), (371/17179869184), by norm_num⟩
  | 7 => ⟨((-926024455/34359738368), (497443169/17179869184)), (167/17179869184), by norm_num⟩
  | 8 => ⟨((5670985/536870912), (-779865089/68719476736)), (33/8589934592), by norm_num⟩
  | 9 => ⟨((-1011560713/274877906944), (543391661/137438953472)), (185/137438953472), by norm_num⟩
  | 10 => ⟨((634348553/549755813888), (-170380141/137438953472)), (117/274877906944), by norm_num⟩
  | 11 => ⟨((-90408919/274877906944), (388527961/1099511627776)), (269/2199023255552), by norm_num⟩
  | 12 => ⟨((755937713/8796093022208), (-812151449/8796093022208)), (71/2199023255552), by norm_num⟩
  | 13 => ⟨((-182326025/8796093022208), (783537283/35184372088832)), (69/8796093022208), by norm_num⟩
  | 14 => ⟨((326675541/70368744177664), (-701936177/140737488355328)), (249/140737488355328), by norm_num⟩
  | 15 => ⟨((-273143805/281474976710656), (586911153/562949953421312)), (105/281474976710656), by norm_num⟩
  | 16 => ⟨((856440821/4503599627370496), (-920128263/4503599627370496)), (83/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1069745559747/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888898967426329/316912650057057350374175801344), (-632336249217/316912650057057350374175801344)), (184649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944324945329447/19807040628566084398385987584), (-1422425109301/39614081257132168796771975168)), (207747/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944178503159637/1237940039285380274899124224), (-755454978423/1237940039285380274899124224)), (220749/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770023581725231/154742504910672534362390528), (-755220690813/77371252455336267181195264)), (110385/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387114902490901/2417851639229258349412352), (-353885283383/2417851639229258349412352)), (206995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257831941153003/604462909807314587353088), (-619050527277/302231454903657293676544)), (181143/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943118993481229/37778931862957161709568), (-2010981995463/75557863725914323419136)), (294399/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648187238294477/2361183241434822606848), (-1507421282129/4722366482869645213696)), (220835/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404961797915589/147573952589676412928), (-1035690216083/295147905179352825856)), (75927/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821474843027301/73786976294838206464), (-40425646175/1152921504606846976)), (379725/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820409026317899/9223372036854775808), (-2907920804853/9223372036854775808)), (427313/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795829937386567/576460752303423488), (-726129363319/288230376151711744)), (106867/288230376151711744), by norm_num⟩
  | 5 => ⟨((596274078665915/72057594037927936), (-2537629217235/144115188075855872)), (5847/2251799813685248), by norm_num⟩
  | 4 => ⟨((744296875388337/18014398509481984), (-1899404869353/18014398509481984)), (140415/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485462302744553/9007199254740992), (-4735181768057/9007199254740992)), (351343/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220384820691629/4503599627370496), (-9430489052011/4503599627370496)), (703605/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204827369441159/2251799813685248), (-14046454775947/2251799813685248)), (1057719/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158453085064617/2251799813685248), (-27698229590135/2251799813685248)), (2124755/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158453085064617/2251799813685248), (-27698229590135/2251799813685248)), (8105297092918014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034317637871881/1125899906842624), (-53100039129865/2251799813685248)), (4125621/1125899906842624), by norm_num⟩
  | 2 => ⟨((949558718298577/1125899906842624), (-12195201969091/281474976710656)), (7774649/1125899906842624), by norm_num⟩
  | 3 => ⟨((1597446072807013/2251799813685248), (-164562555243639/2251799813685248)), (27575239/2251799813685248), by norm_num⟩
  | 4 => ⟨((1121215618543939/2251799813685248), (-58371043022429/562949953421312)), (43154645/2251799813685248), by norm_num⟩
  | 5 => ⟨((1068131898174627/4503599627370496), (-465025529958379/4503599627370496)), (103848645/4503599627370496), by norm_num⟩
  | 6 => ⟨((102657550059011/2251799813685248), (-882331722376693/18014398509481984)), (70706253/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1278750261/16777216)), (1/8388608), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1296107371/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-326690366644737/18014398509481984), (-1115079406085119/18014398509481984)), (202629549/9007199254740992), by norm_num⟩
  | 1 => ⟨((247535603/4294967296), (844903559/4294967296)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((-6145949/67108864), (-41955453/134217728)), (123/1073741824), by norm_num⟩
  | 3 => ⟨((416686011/4294967296), (711129003/2147483648)), (523/4294967296), by norm_num⟩
  | 4 => ⟨((-331062643/4294967296), (-565001563/2147483648)), (417/4294967296), by norm_num⟩
  | 5 => ⟨((52606745/1073741824), (1436484305/8589934592)), (133/2147483648), by norm_num⟩
  | 6 => ⟨((-111458045/4294967296), (-760870741/8589934592)), (283/8589934592), by norm_num⟩
  | 7 => ⟨((101205619/8589934592), (690882335/17179869184)), (129/8589934592), by norm_num⟩
  | 8 => ⟨((-321636905/68719476736), (-1097830625/68719476736)), (103/17179869184), by norm_num⟩
  | 9 => ⟨((454301955/274877906944), (193831379/34359738368)), (73/34359738368), by norm_num⟩
  | 10 => ⟨((-144379607/274877906944), (-492805245/274877906944)), (373/549755813888), by norm_num⟩
  | 11 => ⟨((83426575/549755813888), (1139026615/2199023255552)), (433/2199023255552), by norm_num⟩
  | 12 => ⟨((-353512195/8796093022208), (-1206629299/8796093022208)), (461/8796093022208), by norm_num⟩
  | 13 => ⟨((345686395/35184372088832), (1179917805/35184372088832)), (453/35184372088832), by norm_num⟩
  | 14 => ⟨((-313888563/140737488355328), (-535691757/70368744177664)), (413/140737488355328), by norm_num⟩
  | 15 => ⟨((33251825/70368744177664), (907977195/562949953421312)), (11/17592186044416), by norm_num⟩
  | 16 => ⟨((-422704359/4503599627370496), (-1442800201/4503599627370496)), (561/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-151086323065/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888868942381897/316912650057057350374175801344), (-2857698313249/633825300114114700748351602688)), (184963/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944291078688765/19807040628566084398385987584), (-3214145763167/39614081257132168796771975168)), (26015/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888284800385817/2475880078570760549798248448), (-3414074749941/2475880078570760549798248448)), (221169/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769951106895407/154742504910672534362390528), (-1706500337143/77371252455336267181195264)), (6913/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774195689679309/4835703278458516698824704), (-399818416597/1208925819614629174706176)), (207441/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257771954203545/604462909807314587353088), (-699397143377/151115727451828646838272)), (181561/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886139974074295/75557863725914323419136), (-4543944259569/75557863725914323419136)), (147565/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324075125046891/1180591620717411303424), (-3406089138581/4722366482869645213696)), (110715/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809872358392995/295147905179352825856), (-2340168583409/295147905179352825856)), (38075/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910672807701785/36893488147419103232), (-1461467884813/18446744073709551616)), (47619/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910131044565297/4611686018427387904), (-6570354505133/9223372036854775808)), (428847/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591510997207721/1152921504606846976), (-205079641335/36028797018963968)), (214597/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192415713070167/144115188075855872), (-716682357297/18014398509481984)), (375935/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488390747898697/36028797018963968), (-8582672640965/36028797018963968)), (564683/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485200996872073/9007199254740992), (-5348874043583/4503599627370496)), (707223/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109919848968639/2251799813685248), (-21303956336603/4503599627370496)), (354641/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203953915974217/2251799813685248), (-31727917331503/2251799813685248)), (2138173/2251799813685248), by norm_num⟩
  | 0 => ⟨((539121533159973/562949953421312), (-62548747349091/2251799813685248)), (4317859/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539121533159973/562949953421312), (-62548747349091/2251799813685248)), (16471324929244231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2063469437307049/2251799813685248), (-7487649737587/140737488355328)), (8510065/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884516322841153/2251799813685248), (-219565327921187/2251799813685248)), (16502165/2251799813685248), by norm_num⟩
  | 3 => ⟨((1555730139304147/2251799813685248), (-183752766068611/1125899906842624)), (15419623/1125899906842624), by norm_num⟩
  | 4 => ⟨((507424313719937/1125899906842624), (-507806625821847/2251799813685248)), (26339437/1125899906842624), by norm_num⟩
  | 5 => ⟨((685718297599915/4503599627370496), (-457719957243241/2251799813685248)), (8905295/281474976710656), by norm_num⟩
  | 6 => ⟨((-326690366644737/18014398509481984), (-1115079406085119/18014398509481984)), (202629549/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1296107371/16777216)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1312755827/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1073791078641349/18014398509481984), (-81124235026827/4503599627370496)), (395150925/18014398509481984), by norm_num⟩
  | 1 => ⟨((1648140023/8589934592), (249031867/4294967296)), (609/8589934592), by norm_num⟩
  | 2 => ⟨((-1326289519/4294967296), (-25050083/268435456)), (123/1073741824), by norm_num⟩
  | 3 => ⟨((1423053757/4294967296), (430043235/4294967296)), (265/2147483648), by norm_num⟩
  | 4 => ⟨((-572579167/2147483648), (-346063943/4294967296)), (107/1073741824), by norm_num⟩
  | 5 => ⟨((1474448991/8589934592), (55696843/1073741824)), (553/8589934592), by norm_num⟩
  | 6 => ⟨((-791011369/8589934592), (-478083257/17179869184)), (149/4294967296), by norm_num⟩
  | 7 => ⟨((1454952785/34359738368), (13740095/1073741824)), (275/17179869184), by norm_num⟩
  | 8 => ⟨((-1170828087/68719476736), (-353821277/68719476736)), (111/17179869184), by norm_num⟩
  | 9 => ⟨((418750025/68719476736), (126545195/68719476736)), (319/137438953472), by norm_num⟩
  | 10 => ⟨((-539161733/274877906944), (-325866615/549755813888)), (103/137438953472), by norm_num⟩
  | 11 => ⟨((1262177941/2199023255552), (381426971/2199023255552)), (121/549755813888), by norm_num⟩
  | 12 => ⟨((-1354264687/8796093022208), (-51156919/1099511627776)), (521/8796093022208), by norm_num⟩
  | 13 => ⟨((670647671/17592186044416), (405336049/35184372088832)), (259/17592186044416), by norm_num⟩
  | 14 => ⟨((-308390225/35184372088832), (-186389487/70368744177664)), (239/70368744177664), by norm_num⟩
  | 15 => ⟨((1058847829/562949953421312), (319981127/562949953421312)), (103/140737488355328), by norm_num⟩
  | 16 => ⟨((-106509365/281474976710656), (-257494879/2251799813685248)), (333/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-3709995673721/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777677730947245/633825300114114700748351602688), (-4385502697925/633825300114114700748351602688)), (11579/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944257088206483/19807040628566084398385987584), (-1233121581161/9903520314283042199192993792)), (104239/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888212154023233/2475880078570760549798248448), (-1309820075915/618970019642690137449562112)), (55393/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884938996215175/77371252455336267181195264), (-5237608484871/154742504910672534362390528)), (221645/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774161168813425/4835703278458516698824704), (-4908482140931/9671406556917033397649408)), (207869/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157213880782543/75557863725914323419136), (-4293146614399/604462909807314587353088)), (90981/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471510017227737/18889465931478580854784), (-6973035816763/75557863725914323419136)), (295833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648112379412383/2361183241434822606848), (-1306716634693/1180591620717411303424)), (111001/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619639254074863/590295810358705651712), (-7182214425137/590295810358705651712)), (305457/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455302953233621/18446744073709551616), (-4485340650743/36893488147419103232)), (191065/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455027213138335/2305843009213693952), (-2520569624329/2305843009213693952)), (215161/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795677191480701/576460752303423488), (-5035057734791/576460752303423488)), (430853/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192274887163777/144115188075855872), (-8797680598077/144115188075855872)), (377595/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488171960697325/36028797018963968), (-13169212445373/36028797018963968)), (283795/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484914367343765/9007199254740992), (-8206899363759/4503599627370496)), (177897/2251799813685248), by norm_num⟩
  | 2 => ⟨((277403407233891/562949953421312), (-8171184712307/1125899906842624)), (357373/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101469097314655/1125899906842624), (-1520968234353/70368744177664)), (1080035/1125899906842624), by norm_num⟩
  | 0 => ⟨((1077035883466541/1125899906842624), (-95923599470589/2251799813685248)), (1095945/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077035883466541/1125899906842624), (-95923599470589/2251799813685248)), (4180698396922874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1028249450066369/1125899906842624), (-11470064753671/140737488355328)), (8760535/2251799813685248), by norm_num⟩
  | 2 => ⟨((1863179724091375/2251799813685248), (-335208135743069/2251799813685248)), (17429413/2251799813685248), by norm_num⟩
  | 3 => ⟨((186466075357931/281474976710656), (-277357249108581/1125899906842624)), (34031987/2251799813685248), by norm_num⟩
  | 4 => ⟨((851561510226081/2251799813685248), (-734952972626233/2251799813685248)), (30928383/1125899906842624), by norm_num⟩
  | 5 => ⟨((82157007297917/2251799813685248), (-555873270360101/2251799813685248)), (174325723/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1073791078641349/18014398509481984), (-81124235026827/4503599627370496)), (395150925/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1312755827/16777216)), (1/8388608), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-10380869/131072)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-13386655655433/281474976710656), (664827065174001/18014398509481984)), (199292363/9007199254740992), by norm_num⟩
  | 1 => ⟨((41594521/268435456), (-516431513/4294967296)), (311/4294967296), by norm_num⟩
  | 2 => ⟨((-1084151719/4294967296), (420645931/2147483648)), (509/4294967296), by norm_num⟩
  | 3 => ⟨((588711827/2147483648), (-456835017/2147483648)), (555/4294967296), by norm_num⟩
  | 4 => ⟨((-959039983/4294967296), (372103147/2147483648)), (227/2147483648), by norm_num⟩
  | 5 => ⟨((312464485/2147483648), (-242469595/2147483648)), (297/4294967296), by norm_num⟩
  | 6 => ⟨((-678692971/8589934592), (526659565/8589934592)), (81/2147483648), by norm_num⟩
  | 7 => ⟨((78973115/2147483648), (-30641209/1073741824)), (303/17179869184), by norm_num⟩
  | 8 => ⟨((-514604065/34359738368), (99832017/8589934592)), (31/4294967296), by norm_num⟩
  | 9 => ⟨((372584383/68719476736), (-36140261/8589934592)), (361/137438953472), by norm_num⟩
  | 10 => ⟨((-971132711/549755813888), (753590139/549755813888)), (59/68719476736), by norm_num⟩
  | 11 => ⟨((287640375/549755813888), (-892825245/2199023255552)), (561/2199023255552), by norm_num⟩
  | 12 => ⟨((-624773407/4398046511104), (484818473/4398046511104)), (153/2199023255552), by norm_num⟩
  | 13 => ⟨((626329869/17592186044416), (-486026273/17592186044416)), (77/4398046511104), by norm_num⟩
  | 14 => ⟨((-145760227/17592186044416), (904868867/140737488355328)), (575/140737488355328), by norm_num⟩
  | 15 => ⟨((1013121901/562949953421312), (-393086683/281474976710656)), (501/562949953421312), by norm_num⟩
  | 16 => ⟨((-51575765/140737488355328), (640357181/2251799813685248)), (205/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (808161049597/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777628129249467/633825300114114700748351602688), (3821022641615/633825300114114700748351602688)), (185153/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944229262198167/19807040628566084398385987584), (4297595622907/39614081257132168796771975168)), (104173/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888153223516395/2475880078570760549798248448), (2282442615939/1237940039285380274899124224)), (221423/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769819286428511/154742504910672534362390528), (4563411826721/154742504910672534362390528)), (221487/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24191680298421/151115727451828646838272), (4276633594941/9671406556917033397649408)), (207711/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314415833921535/151115727451828646838272), (3740489965401/604462909807314587353088)), (90907/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942981492643863/37778931862957161709568), (3037682041089/37778931862957161709568)), (147787/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324041833990413/1180591620717411303424), (4553958658725/4722366482869645213696)), (221791/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619560930311771/590295810358705651712), (6257528240653/590295810358705651712)), (305141/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455278713943279/18446744073709551616), (7815666846533/73786976294838206464)), (381695/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820001076234383/9223372036854775808), (1098005852269/1152921504606846976)), (429777/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795624114340383/576460752303423488), (8773333382759/1152921504606846976)), (13445/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192183822057275/144115188075855872), (7664627213883/144115188075855872)), (188491/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488038990574387/36028797018963968), (11472894609521/36028797018963968)), (141629/9007199254740992), by norm_num⟩
  | 3 => ⟨((742377237694229/4503599627370496), (1787388888015/1125899906842624)), (88747/1125899906842624), by norm_num⟩
  | 2 => ⟨((554731581587635/1125899906842624), (28472495358559/4503599627370496)), (1425455/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202533545522017/2251799813685248), (21197728041239/1125899906842624)), (2151985/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153447173932653/2251799813685248), (83543937200453/2251799813685248)), (2179721/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153447173932653/2251799813685248), (83543937200453/2251799813685248)), (8314975742820357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257036344512883/281474976710656), (79894959742931/1125899906842624)), (4330773/1125899906842624), by norm_num⟩
  | 2 => ⟨((1866417622793653/2251799813685248), (145916405339555/1125899906842624)), (8524153/1125899906842624), by norm_num⟩
  | 3 => ⟨((1509169835005971/2251799813685248), (30235919366067/140737488355328)), (16340047/1125899906842624), by norm_num⟩
  | 4 => ⟨((907521001012171/2251799813685248), (324228732331315/1125899906842624)), (903855/35184372088832), by norm_num⟩
  | 5 => ⟨((179011154256091/2251799813685248), (522683023480081/2251799813685248)), (19985847/562949953421312), by norm_num⟩
  | 6 => ⟨((-13386655655433/281474976710656), (664827065174001/18014398509481984)), (199292363/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-10380869/131072)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1344142889/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((3436068560731/9007199254740992), (131210692098045/2251799813685248)), (682310833/36028797018963968), by norm_num⟩
  | 1 => ⟨((-337503/268435456), (-412415539/2147483648)), (269/4294967296), by norm_num⟩
  | 2 => ⟨((8898839/4294967296), (679627169/2147483648)), (445/4294967296), by norm_num⟩
  | 3 => ⟨((-4888187/2147483648), (-1493293519/4294967296)), (245/2147483648), by norm_num⟩
  | 4 => ⟨((8055333/4294967296), (615206479/2147483648)), (203/2147483648), by norm_num⟩
  | 5 => ⟨((-10619625/8589934592), (-1622096155/8589934592)), (537/8589934592), by norm_num⟩
  | 6 => ⟨((11666851/17179869184), (1782054769/17179869184)), (37/1073741824), by norm_num⟩
  | 7 => ⟨((-1373287/4294967296), (-1678103373/34359738368)), (35/2147483648), by norm_num⟩
  | 8 => ⟨((2263065/17179869184), (345672185/17179869184)), (463/68719476736), by norm_num⟩
  | 9 => ⟨((-13259899/274877906944), (-2025385121/274877906944)), (681/274877906944), by norm_num⟩
  | 10 => ⟨((8740493/549755813888), (667533895/274877906944)), (225/274877906944), by norm_num⟩
  | 11 => ⟨((-327355/68719476736), (-1600060233/2199023255552)), (541/2199023255552), by norm_num⟩
  | 12 => ⟨((11508359/8796093022208), (1757845835/8796093022208)), (597/8796093022208), by norm_num⟩
  | 13 => ⟨((-11670669/35184372088832), (-1782637879/35184372088832)), (607/35184372088832), by norm_num⟩
  | 14 => ⟨((2747473/35184372088832), (1678652469/140737488355328)), (287/70368744177664), by norm_num⟩
  | 15 => ⟨((-1207363/70368744177664), (-1475350585/562949953421312)), (507/562949953421312), by norm_num⟩
  | 16 => ⟨((7958543/2251799813685248), (151953589/281474976710656)), (419/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (509402427637/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777582733367111/633825300114114700748351602688), (2408348581701/633825300114114700748351602688)), (92437/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888407724218579/39614081257132168796771975168), (1354363723981/19807040628566084398385987584)), (208015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118006225710571/154742504910672534362390528), (1438594226515/1237940039285380274899124224)), (221051/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769766082229721/154742504910672534362390528), (1438125065073/77371252455336267181195264)), (221091/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548218093245409/9671406556917033397649408), (1347743959409/4835703278458516698824704)), (207315/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628810251619623/302231454903657293676544), (1178777894719/302231454903657293676544)), (45361/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885894192960911/75557863725914323419136), (1914580663983/37778931862957161709568)), (73731/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324029112487635/1180591620717411303424), (2870238451111/4722366482869645213696)), (221263/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619492111305431/590295810358705651712), (3943926730009/590295810358705651712)), (304349/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821030553069195/73786976294838206464), (1231483688521/18446744073709551616)), (190303/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819908597541213/9223372036854775808), (2768108886857/4611686018427387904)), (3347/72057594037927936), by norm_num⟩
  | 6 => ⟨((397789673851797/288230376151711744), (5529401669911/1152921504606846976)), (107177/288230376151711744), by norm_num⟩
  | 5 => ⟨((149013598072459/18014398509481984), (2415284272913/72057594037927936)), (375449/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487933019026795/36028797018963968), (7230562459635/36028797018963968)), (563833/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484633481139837/9007199254740992), (9011502169291/9007199254740992)), (705947/9007199254740992), by norm_num⟩
  | 2 => ⟨((277339817137793/562949953421312), (4485782519157/1125899906842624)), (1415371/4503599627370496), by norm_num⟩
  | 1 => ⟨((550576655755175/562949953421312), (26715807076109/2251799813685248)), (266473/281474976710656), by norm_num⟩
  | 0 => ⟨((2153327976479707/2251799813685248), (52640831944265/2251799813685248)), (4298669/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153327976479707/2251799813685248), (52640831944265/2251799813685248)), (16398120888716887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2057931743727439/2251799813685248), (50338833604059/1125899906842624)), (8422357/2251799813685248), by norm_num⟩
  | 2 => ⟨((117265837850283/140737488355328), (184019703681327/2251799813685248)), (16147599/2251799813685248), by norm_num⟩
  | 3 => ⟨((1548300861164809/2251799813685248), (306659227549511/2251799813685248)), (29548333/2251799813685248), by norm_num⟩
  | 4 => ⟨((1022824347370855/2251799813685248), (13178368010709/70368744177664)), (24340965/1125899906842624), by norm_num⟩
  | 5 => ⟨((192808479614719/1125899906842624), (191550322767375/1125899906842624)), (15614757/562949953421312), by norm_num⟩
  | 6 => ⟨((3436068560731/9007199254740992), (131210692098045/2251799813685248)), (682310833/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1344142889/16777216)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile029Terms3

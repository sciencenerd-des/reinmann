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
namespace Reinmann.XiBand97.Tile002Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9561/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9561/640))
  have he : value ((69/80), (9561/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-1549452281/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-22875260050049/562949953421312), (-1016335523688295/18014398509481984)), (57100983/4503599627370496), by norm_num⟩
  | 1 => ⟨((67432785/536870912), (749000609/4294967296)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((-833750405/4294967296), (-289399085/1073741824)), (265/4294967296), by norm_num⟩
  | 3 => ⟨((107381579/536870912), (1192726477/4294967296)), (275/4294967296), by norm_num⟩
  | 4 => ⟨((-663842039/4294967296), (-230423011/1073741824)), (107/2147483648), by norm_num⟩
  | 5 => ⟨((410392785/4294967296), (1139595695/8589934592)), (267/8589934592), by norm_num⟩
  | 6 => ⟨((-845694347/17179869184), (-587089779/8589934592)), (139/8589934592), by norm_num⟩
  | 7 => ⟨((186719795/8589934592), (259245633/8589934592)), (247/34359738368), by norm_num⟩
  | 8 => ⟨((-577158813/68719476736), (-801339257/68719476736)), (193/68719476736), by norm_num⟩
  | 9 => ⟨((792898841/274877906944), (8600603/2147483648)), (67/68719476736), by norm_num⟩
  | 10 => ⟨((-122544199/137438953472), (-340285811/274877906944)), (167/549755813888), by norm_num⟩
  | 11 => ⟨((275483143/1099511627776), (382486505/1099511627776)), (95/1099511627776), by norm_num⟩
  | 12 => ⟨((-567686727/8796093022208), (-788188017/8796093022208)), (99/4398046511104), by norm_num⟩
  | 13 => ⟨((539921161/35184372088832), (374818865/17592186044416)), (95/17592186044416), by norm_num⟩
  | 14 => ⟨((-238417033/70368744177664), (-662046299/140737488355328)), (85/70368744177664), by norm_num⟩
  | 15 => ⟨((786087649/1125899906842624), (545710191/562949953421312)), (141/562949953421312), by norm_num⟩
  | 16 => ⟨((-303728787/2251799813685248), (-210851671/1125899906842624)), (55/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-2859205547029/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111115731736013/39614081257132168796771975168), (-105638077493/19807040628566084398385987584)), (92533/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888710081500219/39614081257132168796771975168), (-1901042644195/19807040628566084398385987584)), (52061/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236052569190457/309485009821345068724781056), (-4038616202847/2475880078570760549798248448)), (55327/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((55315208536767/4835703278458516698824704), (-4037379772159/154742504910672534362390528)), (55341/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387129568586817/2417851639229258349412352), (-1891865122471/4835703278458516698824704)), (51897/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257882789070953/604462909807314587353088), (-3309451140769/604462909807314587353088)), (45425/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943159854671411/37778931862957161709568), (-1343849388413/18889465931478580854784)), (73843/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648217488497483/2361183241434822606848), (-4029396177713/4722366482869645213696)), (55407/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809964547727561/295147905179352825856), (-5536924627475/590295810358705651712)), (152447/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821575299387041/73786976294838206464), (-3457958183957/36893488147419103232)), (95339/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910259699985143/4611686018427387904), (-7773207009959/9223372036854775808)), (53669/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397941739017551/288230376151711744), (-7764216316911/1152921504606846976)), (6715/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192638159636235/144115188075855872), (-1695896413747/36028797018963968)), (188251/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488721391695647/36028797018963968), (-10155198488751/36028797018963968)), (141419/18014398509481984), by norm_num⟩
  | 3 => ⟨((742804512922005/4503599627370496), (-791171524257/562949953421312)), (88589/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220640007629811/4503599627370496), (-12605986215377/2251799813685248)), (88893/562949953421312), by norm_num⟩
  | 1 => ⟨((1102557642875415/1125899906842624), (-37555023572961/2251799813685248)), (536407/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079327070640985/1125899906842624), (-74063432857367/2251799813685248)), (1085067/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079327070640985/1125899906842624), (-74063432857367/2251799813685248)), (4139202122214889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2066925435067893/2251799813685248), (-141999599683297/2251799813685248)), (4303489/2251799813685248), by norm_num⟩
  | 2 => ⟨((472068702774873/562949953421312), (-260682661550207/2251799813685248)), (2110775/562949953421312), by norm_num⟩
  | 3 => ⟨((388314526333913/562949953421312), (-437197392507143/2251799813685248)), (4028747/562949953421312), by norm_num⟩
  | 4 => ⟨((61658155852569/140737488355328), (-18848267212083/70368744177664)), (1780585/140737488355328), by norm_num⟩
  | 5 => ⟨((541308389880977/4503599627370496), (-264242179881303/1125899906842624)), (80449115/4503599627370496), by norm_num⟩
  | 6 => ⟨((-22875260050049/562949953421312), (-1016335523688295/18014398509481984)), (57100983/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-1549452281/33554432)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-785867347/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-18087499312331/281474976710656), (-336065850079599/18014398509481984)), (211605143/18014398509481984), by norm_num⟩
  | 1 => ⟨((865375511/4294967296), (62807353/1073741824)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-678344977/2147483648), (-49233023/536870912)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((1417964501/4294967296), (411652957/4294967296)), (133/2147483648), by norm_num⟩
  | 4 => ⟨((-1111504873/4294967296), (-161341933/2147483648)), (211/4294967296), by norm_num⟩
  | 5 => ⟨((174255855/1073741824), (202354679/4294967296)), (133/4294967296), by norm_num⟩
  | 6 => ⟨((-1457008601/17179869184), (-211493975/8589934592)), (35/2147483648), by norm_num⟩
  | 7 => ⟨((652634577/17179869184), (378936077/34359738368)), (253/34359738368), by norm_num⟩
  | 8 => ⟨((-511582985/34359738368), (-297037969/68719476736)), (25/8589934592), by norm_num⟩
  | 9 => ⟨((1425835991/274877906944), (103484537/68719476736)), (281/274877906944), by norm_num⟩
  | 10 => ⟨((-223535025/137438953472), (-129790067/274877906944)), (89/274877906944), by norm_num⟩
  | 11 => ⟨((254870101/549755813888), (295968003/2199023255552)), (51/549755813888), by norm_num⟩
  | 12 => ⟨((-532762485/4398046511104), (-38666915/1099511627776)), (215/8796093022208), by norm_num⟩
  | 13 => ⟨((1027983809/35184372088832), (37304581/4398046511104)), (209/35184372088832), by norm_num⟩
  | 14 => ⟨((-920924939/140737488355328), (-133678055/70368744177664)), (189/140737488355328), by norm_num⟩
  | 15 => ⟨((1540029237/1125899906842624), (223544943/562949953421312)), (159/562949953421312), by norm_num⟩
  | 16 => ⟨((-1207188191/4503599627370496), (-175230969/2251799813685248)), (251/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1862113906125/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777788394585673/633825300114114700748351602688), (-2201424651471/316912650057057350374175801344)), (46317/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944319318589409/19807040628566084398385987584), (-4952024909145/39614081257132168796771975168)), (52121/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944172175279817/1237940039285380274899124224), (-2630036318223/1237940039285380274899124224)), (110789/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442502535137859/38685626227668133590597632), (-5258437429063/154742504910672534362390528)), (110825/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548446175053843/9671406556917033397649408), (-4928048137003/9671406556917033397649408)), (103937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628909676288849/302231454903657293676544), (-134697052447/18889465931478580854784)), (11373/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886215970254251/75557863725914323419136), (-7000991985639/75557863725914323419136)), (147921/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296356600473925/4722366482869645213696), (-5247897176783/4722366482869645213696)), (27751/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202477549910181/73786976294838206464), (-1802808646301/147573952589676412928)), (76367/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455359509722159/18446744073709551616), (-4503555374019/36893488147419103232)), (5971/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820363074176149/9223372036854775808), (-632717076385/576460752303423488)), (215169/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591608251457309/1152921504606846976), (-2527893488763/288230376151711744)), (53859/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192496624958469/144115188075855872), (-8834252492755/144115188075855872)), (188807/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488503773435829/36028797018963968), (-13224659204595/36028797018963968)), (283811/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485327744589091/9007199254740992), (-2060516514763/1125899906842624)), (355817/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110024924670333/2251799813685248), (-16414228931035/2251799813685248)), (357401/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102080842521133/1125899906842624), (-1527941056173/70368744177664)), (270037/562949953421312), by norm_num⟩
  | 0 => ⟨((269559653362143/281474976710656), (-12049949572897/281474976710656)), (548055/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((269559653362143/281474976710656), (-12049949572897/281474976710656)), (2090663912059593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2061062941607171/2251799813685248), (-92318834671841/1125899906842624)), (2193269/1125899906842624), by norm_num⟩
  | 2 => ⟨((1871342805304427/2251799813685248), (-168998085707353/1125899906842624)), (4374657/1125899906842624), by norm_num⟩
  | 3 => ⟨((23506769330173/35184372088832), (-35111175278177/140737488355328)), (4292167/562949953421312), by norm_num⟩
  | 4 => ⟨((864963185456023/2251799813685248), (-375325861648607/1125899906842624)), (31507339/2251799813685248), by norm_num⟩
  | 5 => ⟨((164031723764027/4503599627370496), (-1153363814678719/4503599627370496)), (90423185/4503599627370496), by norm_num⟩
  | 6 => ⟨((-18087499312331/281474976710656), (-336065850079599/18014398509481984)), (211605143/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-785867347/16777216)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-796534313/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-545100892504001/9007199254740992), (401980926195535/18014398509481984)), (103392535/9007199254740992), by norm_num⟩
  | 1 => ⟨((826053609/4294967296), (-304583793/4294967296)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-656310709/2147483648), (483991845/4294967296)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((1390527175/4294967296), (-512717379/4294967296)), (135/2147483648), by norm_num⟩
  | 4 => ⟨((-1104792553/4294967296), (407360857/4294967296)), (217/4294967296), by norm_num⟩
  | 5 => ⟨((702218041/4294967296), (-517845893/8589934592)), (139/4294967296), by norm_num⟩
  | 6 => ⟨((-371947789/4294967296), (137145177/4294967296)), (297/17179869184), by norm_num⟩
  | 7 => ⟨((337734313/8589934592), (-62264965/4294967296)), (271/34359738368), by norm_num⟩
  | 8 => ⟨((-1073337827/68719476736), (395762821/68719476736)), (217/68719476736), by norm_num⟩
  | 9 => ⟨((758027865/137438953472), (-279501233/137438953472)), (309/274877906944), by norm_num⟩
  | 10 => ⟨((-30113167/17179869184), (177653993/274877906944)), (99/274877906944), by norm_num⟩
  | 11 => ⟨((139201841/274877906944), (-51326723/274877906944)), (231/2199023255552), by norm_num⟩
  | 12 => ⟨((-4608239/34359738368), (108746059/2199023255552)), (247/8796093022208), by norm_num⟩
  | 13 => ⟨((288398407/8796093022208), (-425354867/35184372088832)), (243/35184372088832), by norm_num⟩
  | 14 => ⟨((-261870189/35184372088832), (386228761/140737488355328)), (223/140737488355328), by norm_num⟩
  | 15 => ⟨((887720061/562949953421312), (-327321545/562949953421312)), (191/562949953421312), by norm_num⟩
  | 16 => ⟨((-705305535/2251799813685248), (520122745/4503599627370496)), (305/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (3632121147279/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777732375524011/633825300114114700748351602688), (134178085573/19807040628566084398385987584)), (5789/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888575659399655/39614081257132168796771975168), (1207311726581/9903520314283042199192993792)), (104229/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888277492751131/2475880078570760549798248448), (5129638048105/2475880078570760549798248448)), (110775/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769943345798573/154742504910672534362390528), (320501378075/9671406556917033397649408)), (55405/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548383621932863/9671406556917033397649408), (4805804147667/9671406556917033397649408)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78610292844709/37778931862957161709568), (4203362639791/604462909807314587353088)), (90969/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235765907707791/9444732965739290427392), (6827247944369/75557863725914323419136)), (18487/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296290178653565/4722366482869645213696), (39981428055/36893488147419103232)), (13873/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619729247252257/590295810358705651712), (879020258613/73786976294838206464)), (152703/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910662182762523/36893488147419103232), (4391676203521/36893488147419103232)), (95515/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455058889462463/2305843009213693952), (9871858513501/9223372036854775808)), (215117/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591481192189777/1152921504606846976), (9860101411041/1152921504606846976)), (215377/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596192980663639/72057594037927936), (8614374477253/144115188075855872)), (47187/36028797018963968), by norm_num⟩
  | 4 => ⟨((744169401019219/18014398509481984), (12895164409677/36028797018963968)), (70927/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485123317018887/9007199254740992), (16072830449381/9007199254740992)), (177831/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219646332612831/4503599627370496), (16003783310151/2251799813685248)), (357207/2251799813685248), by norm_num⟩
  | 1 => ⟨((550892420106175/562949953421312), (47667097486331/2251799813685248)), (539685/1125899906842624), by norm_num⟩
  | 0 => ⟨((538836461760135/562949953421312), (93963085163797/2251799813685248)), (2189883/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((538836461760135/562949953421312), (93963085163797/2251799813685248)), (8353740700728606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029551257354689/1125899906842624), (179876509583205/2251799813685248)), (2187461/1125899906842624), by norm_num⟩
  | 2 => ⟨((1868526492369081/2251799813685248), (328967229652409/2251799813685248)), (8700027/2251799813685248), by norm_num⟩
  | 3 => ⟨((93901881118017/140737488355328), (272974524640719/1125899906842624)), (16980423/2251799813685248), by norm_num⟩
  | 4 => ⟨((435037746855217/1125899906842624), (182132150151375/562949953421312)), (30892929/2251799813685248), by norm_num⟩
  | 5 => ⟨((200974741608959/4503599627370496), (562993990852691/2251799813685248)), (5482899/281474976710656), by norm_num⟩
  | 6 => ⟨((-545100892504001/9007199254740992), (401980926195535/18014398509481984)), (103392535/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-796534313/16777216)), (1/16777216), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-403382885/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-640497367370351/18014398509481984), (920917296558377/18014398509481984)), (102329467/9007199254740992), by norm_num⟩
  | 1 => ⟨((122885793/1073741824), (-353374293/2147483648)), (159/4294967296), by norm_num⟩
  | 2 => ⟨((-791108217/4294967296), (1137467969/4294967296)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((212206593/1073741824), (-1220456049/4294967296)), (279/4294967296), by norm_num⟩
  | 4 => ⟨((-42691667/268435456), (491062059/2147483648)), (113/2147483648), by norm_num⟩
  | 5 => ⟨((879482719/8589934592), (-158066779/1073741824)), (293/8589934592), by norm_num⟩
  | 6 => ⟨((-471824277/8589934592), (678396445/8589934592)), (159/8589934592), by norm_num⟩
  | 7 => ⟨((867853577/34359738368), (-1247813667/34359738368)), (295/34359738368), by norm_num⟩
  | 8 => ⟨((-698378225/68719476736), (62758707/4294967296)), (239/68719476736), by norm_num⟩
  | 9 => ⟨((15611061/4294967296), (-718266613/137438953472)), (173/137438953472), by norm_num⟩
  | 10 => ⟨((-80400107/68719476736), (924804415/549755813888)), (225/549755813888), by norm_num⟩
  | 11 => ⟨((752866795/2199023255552), (-1082483845/2199023255552)), (265/2199023255552), by norm_num⟩
  | 12 => ⟨((-807794909/8796093022208), (145182545/1099511627776)), (143/4398046511104), by norm_num⟩
  | 13 => ⟨((200014731/8796093022208), (-575168719/17592186044416)), (143/17592186044416), by norm_num⟩
  | 14 => ⟨((-735797237/140737488355328), (1057940963/140737488355328)), (265/140737488355328), by norm_num⟩
  | 15 => ⟨((39473999/35184372088832), (-908101491/562949953421312)), (229/562949953421312), by norm_num⟩
  | 16 => ⟨((-127061901/562949953421312), (182691621/562949953421312)), (93/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (709433346025/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777682012712783/633825300114114700748351602688), (3354421003807/633825300114114700748351602688)), (92531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888519226183229/39614081257132168796771975168), (943202912893/9903520314283042199192993792)), (104119/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888217832974475/2475880078570760549798248448), (2003738238399/1237940039285380274899124224)), (110651/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442471005937045/38685626227668133590597632), (4006199055851/154742504910672534362390528)), (55339/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387082091514257/2417851639229258349412352), (1877227407283/4835703278458516698824704)), (103791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257716694846769/604462909807314587353088), (820947919775/151115727451828646838272)), (45423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235756243475787/9444732965739290427392), (5333619544283/75557863725914323419136)), (4615/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1296232779682537/4722366482869645213696), (3997991562977/4722366482869645213696)), (110809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619651275314323/590295810358705651712), (1373406981483/147573952589676412928)), (19055/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455307081455837/18446744073709551616), (3430811397629/36893488147419103232)), (47667/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820129469211101/9223372036854775808), (963986229225/1152921504606846976)), (26833/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795688771555095/576460752303423488), (3851301915237/576460752303423488)), (214867/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192298005371735/144115188075855872), (6729343635511/144115188075855872)), (94119/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488212323326777/36028797018963968), (1259147011455/4503599627370496)), (141407/18014398509481984), by norm_num⟩
  | 3 => ⟨((742487361574909/4503599627370496), (12555068826643/9007199254740992)), (177161/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109688745195313/2251799813685248), (6250300962159/1125899906842624)), (355529/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101618347314089/1125899906842624), (18615207511857/1125899906842624)), (536323/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154957483315771/2251799813685248), (73380918057507/2251799813685248)), (2169641/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154957483315771/2251799813685248), (73380918057507/2251799813685248)), (8276523598677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2059888702172187/2251799813685248), (70225051773945/1125899906842624)), (536759/281474976710656), by norm_num⟩
  | 2 => ⟨((1875573134024757/2251799813685248), (128480151636451/1125899906842624)), (4195939/1125899906842624), by norm_num⟩
  | 3 => ⟨((1532883146467755/2251799813685248), (214027836044965/1125899906842624)), (15894807/2251799813685248), by norm_num⟩
  | 4 => ⟨((962118865606831/2251799813685248), (291393276395527/1125899906842624)), (27683407/2251799813685248), by norm_num⟩
  | 5 => ⟨((520501460103957/4503599627370496), (498010465810101/2251799813685248)), (75971667/4503599627370496), by norm_num⟩
  | 6 => ⟨((-640497367370351/18014398509481984), (920917296558377/18014398509481984)), (102329467/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-403382885/8388608)), (1/16777216), by norm_num⟩, -8, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-94291587/33554432), (-51037243/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-11807689523159/9007199254740992), (2168364280907163/36028797018963968)), (355209747/36028797018963968), by norm_num⟩
  | 1 => ⟨((1146513/268435456), (-842182655/4294967296)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((-1867725/268435456), (1371956197/4294967296)), (229/4294967296), by norm_num⟩
  | 3 => ⟨((32454551/4294967296), (-1489988579/4294967296)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-26435015/4294967296), (606815829/2147483648)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((8612783/2147483648), (-790825821/4294967296)), (271/8589934592), by norm_num⟩
  | 6 => ⟨((-18707519/8589934592), (429431145/4294967296)), (37/2147483648), by norm_num⟩
  | 7 => ⟨((34829087/34359738368), (-799501787/17179869184)), (139/17179869184), by norm_num⟩
  | 8 => ⟨((-7092283/17179869184), (651213501/34359738368)), (57/17179869184), by norm_num⟩
  | 9 => ⟨((5134965/34359738368), (-1885970181/274877906944)), (83/68719476736), by norm_num⟩
  | 10 => ⟨((-26768339/549755813888), (153616823/68719476736)), (109/274877906944), by norm_num⟩
  | 11 => ⟨((31714121/2199023255552), (-363998865/549755813888)), (65/549755813888), by norm_num⟩
  | 12 => ⟨((-8610639/2199023255552), (1581257923/8796093022208)), (71/2199023255552), by norm_num⟩
  | 13 => ⟨((34528361/35184372088832), (-396299305/8796093022208)), (143/17592186044416), by norm_num⟩
  | 14 => ⟨((-8035481/35184372088832), (1475635879/140737488355328)), (67/35184372088832), by norm_num⟩
  | 15 => ⟨((27925731/562949953421312), (-160258805/70368744177664)), (117/281474976710656), by norm_num⟩
  | 16 => ⟨((-11373091/1125899906842624), (2088554631/4503599627370496)), (383/4503599627370496), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (2074506265049/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888816368571561/316912650057057350374175801344), (1226045138603/316912650057057350374175801344)), (46221/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944231979168483/19807040628566084398385987584), (1378965896567/19807040628566084398385987584)), (104013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888159334501851/2475880078570760549798248448), (2929462596949/2475880078570760549798248448)), (27633/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769825776559265/154742504910672534362390528), (2928518108353/154742504910672534362390528)), (13819/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193534253261349/1208925819614629174706176), (2744482592803/9671406556917033397649408)), (6479/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1257669413907045/604462909807314587353088), (2400419568493/604462909807314587353088)), (11341/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885973615509125/75557863725914323419136), (974700664209/18889465931478580854784)), (147473/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296175966770965/4722366482869645213696), (2922458663885/4722366482869645213696)), (6915/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101223366600145/36893488147419103232), (4015711978569/590295810358705651712)), (152187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910566312029685/36893488147419103232), (5015639963513/73786976294838206464)), (11895/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910011630003493/4611686018427387904), (2818549922085/4611686018427387904)), (214229/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397818287226787/288230376151711744), (5630238292225/1152921504606846976)), (107189/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192208696692787/144115188075855872), (4918749344137/144115188075855872)), (187749/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488082418764451/36028797018963968), (230085339793/1125899906842624)), (140979/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484819413227367/9007199254740992), (573533260199/562949953421312)), (88259/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219087957192027/4503599627370496), (18272645905727/4503599627370496)), (2765/17592186044416), by norm_num⟩
  | 1 => ⟨((1101427336600479/1125899906842624), (27208711443829/2251799813685248)), (133275/281474976710656), by norm_num⟩
  | 0 => ⟨((2154399937941819/2251799813685248), (13405277487839/562949953421312)), (134391/140737488355328), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154399937941819/2251799813685248), (13405277487839/562949953421312)), (512660980761480287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2059936163499331/2251799813685248), (102603539843547/2251799813685248)), (527113/281474976710656), by norm_num⟩
  | 2 => ⟨((939872515660393/1125899906842624), (187722497303937/2251799813685248)), (4049749/1125899906842624), by norm_num⟩
  | 3 => ⟨((1553513605215231/2251799813685248), (313411902274479/2251799813685248)), (3718237/562949953421312), by norm_num⟩
  | 4 => ⟨((1028145347126815/2251799813685248), (432444883653273/2251799813685248)), (6165443/562949953421312), by norm_num⟩
  | 5 => ⟨((193195299185295/1125899906842624), (789797018926403/4503599627370496)), (63985695/4503599627370496), by norm_num⟩
  | 6 => ⟨((-11807689523159/9007199254740992), (2168364280907163/36028797018963968)), (355209747/36028797018963968), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-51037243/1048576)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-103256871/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((541516388556203/18014398509481984), (449623996614933/9007199254740992)), (68984837/9007199254740992), by norm_num⟩
  | 1 => ⟨((-212758741/2147483648), (-353309475/2147483648)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((350609051/2147483648), (1164450393/4294967296)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-96295853/536870912), (-1279279511/4294967296)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((634750845/4294967296), (32939817/134217728)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((-418407047/4294967296), (-694811285/4294967296)), (113/4294967296), by norm_num⟩
  | 6 => ⟨((459667123/8589934592), (95416027/1073741824)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((-432853671/17179869184), (-718801507/17179869184)), (15/2147483648), by norm_num⟩
  | 8 => ⟨((713307543/68719476736), (1184526253/68719476736)), (25/8589934592), by norm_num⟩
  | 9 => ⟨((-16326009/4294967296), (-216889183/34359738368)), (37/34359738368), by norm_num⟩
  | 10 => ⟨((344370319/274877906944), (142966273/68719476736)), (197/549755813888), by norm_num⟩
  | 11 => ⟨((-103180763/274877906944), (-685372383/1099511627776)), (119/1099511627776), by norm_num⟩
  | 12 => ⟨((453422617/4398046511104), (376479261/2199023255552)), (33/1099511627776), by norm_num⟩
  | 13 => ⟨((-459817531/17592186044416), (-381788993/8796093022208)), (17/2199023255552), by norm_num⟩
  | 14 => ⟨((216497653/35184372088832), (719036707/70368744177664)), (65/35184372088832), by norm_num⟩
  | 15 => ⟨((-761110343/562949953421312), (-315977025/140737488355328)), (231/562949953421312), by norm_num⟩
  | 16 => ⟨((313561941/1125899906842624), (130176091/281474976710656)), (3/35184372088832), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (1340087168831/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222198062458153/79228162514264337593543950336), (1583913256647/633825300114114700748351602688)), (92357/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888409806987675/39614081257132168796771975168), (1781467026719/39614081257132168796771975168)), (103911/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888101953640765/2475880078570760549798248448), (1892260113335/2475880078570760549798248448)), (110417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769768569810751/154742504910672534362390528), (1891643260661/154742504910672534362390528)), (110431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774110289804705/4835703278458516698824704), (1772760423205/9671406556917033397649408)), (103543/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314405708228275/151115727451828646838272), (1550510543119/604462909807314587353088)), (45307/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942949133653463/37778931862957161709568), (2518352482519/75557863725914323419136)), (147273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296119757936561/4722366482869645213696), (943845628067/2361183241434822606848)), (55239/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619497069052581/590295810358705651712), (2593832899271/590295810358705651712)), (18993/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821037363100943/73786976294838206464), (1619839694361/36893488147419103232)), (94993/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819917099785903/9223372036854775808), (455131454601/1152921504606846976)), (213811/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795584123147255/576460752303423488), (3636572227999/1152921504606846976)), (53477/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192118317821013/144115188075855872), (397121060755/18014398509481984)), (93639/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487949662568357/36028797018963968), (4755406079665/36028797018963968)), (140567/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484658367371971/9007199254740992), (5926715890895/9007199254740992)), (43975/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109390238358193/2251799813685248), (11800966009001/4503599627370496)), (704749/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202429677599151/2251799813685248), (17570840711463/2251799813685248)), (265003/562949953421312), by norm_num⟩
  | 0 => ⟨((2153693039635379/2251799813685248), (4327821522025/281474976710656)), (2131659/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153693039635379/2251799813685248), (4327821522025/281474976710656)), (8131633767134856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2059328257462037/2251799813685248), (66228260840045/2251799813685248)), (4143125/2251799813685248), by norm_num⟩
  | 2 => ⟨((1881360262888757/2251799813685248), (60567430622203/1125899906842624)), (7821697/2251799813685248), by norm_num⟩
  | 3 => ⟨((1565344646866929/2251799813685248), (50603591183089/562949953421312)), (3477865/562949953421312), by norm_num⟩
  | 4 => ⟨((534979236116439/1125899906842624), (281417771115467/2251799813685248)), (21842181/2251799813685248), by norm_num⟩
  | 5 => ⟨((473228199028649/2251799813685248), (133717627389401/1125899906842624)), (26216367/2251799813685248), by norm_num⟩
  | 6 => ⟨((541516388556203/18014398509481984), (449623996614933/9007199254740992)), (68984837/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-103256871/2097152)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile002Terms3

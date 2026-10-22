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
namespace Reinmann.XiBand97.Tile017Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53817/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53817/2560))
  have he : value ((69/80), (53817/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-1955756865/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-260594596722435/1125899906842624), (-1123481888179855/2251799813685248)), (836549/35184372088832), by norm_num⟩
  | 1 => ⟨((172262583/1073741824), (742662719/2147483648)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((-477613295/8589934592), (-257387285/2147483648)), (53/8589934592), by norm_num⟩
  | 3 => ⟨((110352103/8589934592), (951505445/34359738368)), (51/34359738368), by norm_num⟩
  | 4 => ⟨((-611921993/274877906944), (-1319066633/274877906944)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((678643207/2199023255552), (365722927/549755813888)), (83/2199023255552), by norm_num⟩
  | 6 => ⟨((-627199501/17592186044416), (-1351999017/17592186044416)), (79/17592186044416), by norm_num⟩
  | 7 => ⟨((31052969/8796093022208), (267752659/35184372088832)), (65/140737488355328), by norm_num⟩
  | 8 => ⟨((-344388447/1125899906842624), (-742368003/1125899906842624)), (47/1125899906842624), by norm_num⟩
  | 9 => ⟨((424376677/18014398509481984), (114348953/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | 10 => ⟨((-470648795/288230376151711744), (-126817047/36028797018963968)), (69/288230376151711744), by norm_num⟩
  | 11 => ⟨((237257371/2305843009213693952), (255717465/1152921504606846976)), (71/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-438544741/73786976294838206464), (-945332479/73786976294838206464)), (17/18446744073709551616), by norm_num⟩
  | 13 => ⟨((187062185/590295810358705651712), (806467129/1180591620717411303424)), (15/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-296369431/18889465931478580854784), (-638857619/18889465931478580854784)), (97/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((219122811/302231454903657293676544), (59042981/37778931862957161709568)), (37/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-607537435/19342813113834066795298816), (-654807613/9671406556917033397649408)), (105/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-81623011175/316912650057057350374175801344)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55657603416373/19807040628566084398385987584), (-3098624583669/633825300114114700748351602688)), (23127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892300144312109/39614081257132168796771975168), (-3485754697277/39614081257132168796771975168)), (26023/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946117215720613/1237940039285380274899124224), (-3703387113745/2475880078570760549798248448)), (13827/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773899916515225/154742504910672534362390528), (-1851565688885/77371252455336267181195264)), (27661/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552092515596597/9671406556917033397649408), (-3471413879545/9671406556917033397649408)), (12969/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157626196953113/75557863725914323419136), (-759303820357/151115727451828646838272)), (1419/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((236424934049461/9444732965739290427392), (-616870615915/9444732965739290427392)), (36905/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650121845994421/2361183241434822606848), (-1850388683573/2361183241434822606848)), (13845/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625164278588147/590295810358705651712), (-5087843293691/590295810358705651712)), (9523/147573952589676412928), by norm_num⟩
  | 8 => ⟨((57128643038497/2305843009213693952), (-3179357604381/36893488147419103232)), (47641/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827874621796607/9223372036854775808), (-7152056501667/9223372036854775808)), (26817/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599117530555245/1152921504606846976), (-7150182578787/1152921504606846976)), (3355/72057594037927936), by norm_num⟩
  | 5 => ⟨((299766170104009/36028797018963968), (-1563574956145/36028797018963968)), (23511/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498350700031101/36028797018963968), (-9377225457289/36028797018963968)), (35319/18014398509481984), by norm_num⟩
  | 3 => ⟨((748813656786641/4503599627370496), (-2928532353065/2251799813685248)), (88481/9007199254740992), by norm_num⟩
  | 2 => ⟨((280577682462811/562949953421312), (-11703005997115/2251799813685248)), (22189/562949953421312), by norm_num⟩
  | 1 => ⟨((1120474688502211/1125899906842624), (-8763315664811/562949953421312)), (66911/562949953421312), by norm_num⟩
  | 0 => ⟨((139360520479231/140737488355328), (-8735334658015/281474976710656)), (270405/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139360520479231/140737488355328), (-8735334658015/281474976710656)), (1031513218406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((275722955938495/281474976710656), (-34599474489063/562949953421312)), (34519/70368744177664), by norm_num⟩
  | 2 => ⟨((269025219959685/281474976710656), (-135569697761795/1125899906842624)), (574963/562949953421312), by norm_num⟩
  | 3 => ⟨((1012180526628091/1125899906842624), (-64786696470227/281474976710656)), (2475055/1125899906842624), by norm_num⟩
  | 4 => ⟨((425149853923263/562949953421312), (-465944314610515/1125899906842624)), (2794747/562949953421312), by norm_num⟩
  | 5 => ⟨((224667168800441/562949953421312), (-351889463866391/562949953421312)), (1633613/140737488355328), by norm_num⟩
  | 6 => ⟨((-260594596722435/1125899906842624), (-1123481888179855/2251799813685248)), (836549/35184372088832), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1955756865/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-774950323/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-392739609280691/2251799813685248), (389833031825661/1125899906842624)), (19057403/562949953421312), by norm_num⟩
  | 1 => ⟨((411480485/2147483648), (-816870421/2147483648)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-452057517/4294967296), (897423883/4294967296)), (23/1073741824), by norm_num⟩
  | 3 => ⟨((331090629/8589934592), (-164320151/2147483648)), (137/17179869184), by norm_num⟩
  | 4 => ⟨((-181870117/17179869184), (722096549/34359738368)), (77/34359738368), by norm_num⟩
  | 5 => ⟨((319687593/137438953472), (-317321657/68719476736)), (69/137438953472), by norm_num⟩
  | 6 => ⟨((-58535453/137438953472), (929635925/1099511627776)), (103/1099511627776), by norm_num⟩
  | 7 => ⟨((1148353/17179869184), (-583605401/4398046511104)), (33/2199023255552), by norm_num⟩
  | 8 => ⟨((-40371031/4398046511104), (1282312131/70368744177664)), (37/17592186044416), by norm_num⟩
  | 9 => ⟨((630785575/562949953421312), (-1252234547/562949953421312)), (147/562949953421312), by norm_num⟩
  | 10 => ⟨((-138597757/1125899906842624), (550288105/2251799813685248)), (33/1125899906842624), by norm_num⟩
  | 11 => ⟨((221476653/18014398509481984), (-439675109/18014398509481984)), (27/9007199254740992), by norm_num⟩
  | 12 => ⟨((-648845261/576460752303423488), (80505413/36028797018963968)), (161/576460752303423488), by norm_num⟩
  | 13 => ⟨((54833029/576460752303423488), (-870835555/4611686018427387904)), (111/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-17211497/2305843009213693952), (1093383591/73786976294838206464)), (71/36893488147419103232), by norm_num⟩
  | 15 => ⟨((80677385/147573952589676412928), (-40040155/36893488147419103232)), (169/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-709065333/18889465931478580854784), (1407635403/18889465931478580854784)), (47/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (2653969462695/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780502875842975/633825300114114700748351602688), (786669265787/158456325028528675187087900672)), (46255/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891692194152309/39614081257132168796771975168), (3539701027419/39614081257132168796771975168)), (52047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891588523704389/2475880078570760549798248448), (1880283686347/1237940039285380274899124224)), (55311/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773254053051821/154742504910672534362390528), (1880078362603/77371252455336267181195264)), (13831/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775743532842695/4835703278458516698824704), (3524710583447/9671406556917033397649408)), (6485/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260479854089167/604462909807314587353088), (1541842688213/302231454903657293676544)), (45409/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890538763389151/75557863725914323419136), (2505085218305/37778931862957161709568)), (73815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40612444930305/147573952589676412928), (939227933773/1180591620717411303424)), (6923/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624276905234835/590295810358705651712), (5164589836295/590295810358705651712)), (76189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913503775095395/36893488147419103232), (806748916913/9223372036854775808)), (95291/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826627227719033/9223372036854775808), (7258339134147/9223372036854775808)), (53639/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199733808002223/144115188075855872), (7255337103737/1152921504606846976)), (107373/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197973866860293/144115188075855872), (1586260453529/36028797018963968)), (94057/144115188075855872), by norm_num⟩
  | 4 => ⟨((748357610988725/18014398509481984), (9510804257315/36028797018963968)), (141299/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495584271624975/9007199254740992), (2969168292695/2251799813685248)), (44249/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120269659561999/2251799813685248), (5929457660783/1125899906842624)), (44389/562949953421312), by norm_num⟩
  | 1 => ⟨((139677257300495/140737488355328), (17743944927695/1125899906842624)), (33467/140737488355328), by norm_num⟩
  | 0 => ⟨((69299442571559/70368744177664), (17654989516795/562949953421312)), (541089/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((69299442571559/70368744177664), (17654989516795/562949953421312)), (2064090733054732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((545417429890103/562949953421312), (8693354886593/140737488355328)), (549837/562949953421312), by norm_num⟩
  | 2 => ⟨((1052565970812855/1125899906842624), (67380871078173/562949953421312)), (1133353/562949953421312), by norm_num⟩
  | 3 => ⟨((967878573522713/1125899906842624), (31496055532815/140737488355328)), (4780751/1125899906842624), by norm_num⟩
  | 4 => ⟨((775646956601405/1125899906842624), (216604386343229/562949953421312)), (2589833/281474976710656), by norm_num⟩
  | 5 => ⟨((367668882497187/1125899906842624), (1193772427069749/2251799813685248)), (22245207/1125899906842624), by norm_num⟩
  | 6 => ⟨((-392739609280691/2251799813685248), (389833031825661/1125899906842624)), (19057403/562949953421312), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-774950323/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-1955756865/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-439902948603289/2251799813685248), (260034935428875/1125899906842624)), (60962427/2251799813685248), by norm_num⟩
  | 1 => ⟨((581583955/2147483648), (-687570505/2147483648)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-806246557/4294967296), (476587557/2147483648)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((745130037/8589934592), (-880920857/8589934592)), (109/8589934592), by norm_num⟩
  | 4 => ⟨((-32280299/1073741824), (9540747/268435456)), (39/8589934592), by norm_num⟩
  | 5 => ⟨((572799955/68719476736), (-677185729/68719476736)), (11/8589934592), by norm_num⟩
  | 6 => ⟨((-529379565/274877906944), (625852505/274877906944)), (83/274877906944), by norm_num⟩
  | 7 => ⟨((838715321/2199023255552), (-991560913/2199023255552)), (67/1099511627776), by norm_num⟩
  | 8 => ⟨((-72669145/1099511627776), (687297651/8796093022208)), (95/8796093022208), by norm_num⟩
  | 9 => ⟨((716379207/70368744177664), (-211732635/17592186044416)), (119/70368744177664), by norm_num⟩
  | 10 => ⟨((-198622491/140737488355328), (469638013/281474976710656)), (67/281474976710656), by norm_num⟩
  | 11 => ⟨((801015969/4503599627370496), (-946991315/4503599627370496)), (137/4503599627370496), by norm_num⟩
  | 12 => ⟨((-740295947/36028797018963968), (875205813/36028797018963968)), (129/36028797018963968), by norm_num⟩
  | 13 => ⟨((315774799/144115188075855872), (-373320887/144115188075855872)), (7/18014398509481984), by norm_num⟩
  | 14 => ⟨((-62536689/288230376151711744), (591465875/2305843009213693952)), (45/1152921504606846976), by norm_num⟩
  | 15 => ⟨((739791013/36893488147419103232), (-874608861/36893488147419103232)), (135/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-512784055/295147905179352825856), (303116333/147573952589676412928)), (95/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1480338834343/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780118447592883/633825300114114700748351602688), (3508890630417/633825300114114700748351602688)), (46273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891259681256643/39614081257132168796771975168), (3947067351579/39614081257132168796771975168)), (13017/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945564467020311/1237940039285380274899124224), (2096622822421/1237940039285380274899124224)), (55335/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772794413156677/154742504910672534362390528), (4192667985965/154742504910672534362390528)), (55349/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551056099980231/9671406556917033397649408), (982503113137/2417851639229258349412352)), (25953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260102705869441/604462909807314587353088), (1719073543603/302231454903657293676544)), (45433/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118120362368191/4722366482869645213696), (5585838073413/75557863725914323419136)), (73857/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162392303327643/590295810358705651712), (4188371428019/4722366482869645213696)), (27709/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623644523791299/590295810358705651712), (5757374035639/590295810358705651712)), (4765/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1826216862242497/73786976294838206464), (1798565589937/18446744073709551616)), (95361/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825737414310991/9223372036854775808), (2022542251047/2305843009213693952)), (53683/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596980290061141/1152921504606846976), (8085948411551/1152921504606846976)), (107471/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197194560795559/144115188075855872), (7070456141563/144115188075855872)), (23539/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495545459582583/36028797018963968), (2649046352163/9007199254740992)), (4421/1125899906842624), by norm_num⟩
  | 3 => ⟨((1494120672767231/9007199254740992), (13228605815131/9007199254740992)), (22157/1125899906842624), by norm_num⟩
  | 2 => ⟨((1118803986696531/2251799813685248), (13203660907121/2251799813685248)), (177881/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115214433232037/1125899906842624), (19743108527235/1125899906842624)), (268387/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104363781264253/1125899906842624), (39236565532419/1125899906842624)), (135763/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104363781264253/1125899906842624), (39236565532419/1125899906842624)), (517894745946788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((270468059791695/281474976710656), (76972103136095/1125899906842624)), (275795/281474976710656), by norm_num⟩
  | 2 => ⟨((1034304053265477/1125899906842624), (73962153355843/562949953421312)), (283865/140737488355328), by norm_num⟩
  | 3 => ⟨((930725073975635/1125899906842624), (135890152471403/562949953421312)), (1192267/281474976710656), by norm_num⟩
  | 4 => ⟨((703778927732787/1125899906842624), (112333584400221/281474976710656)), (10187105/1125899906842624), by norm_num⟩
  | 5 => ⟨((32574324590305/140737488355328), (280870472044967/562949953421312)), (41733323/2251799813685248), by norm_num⟩
  | 6 => ⟨((-439902948603289/2251799813685248), (260034935428875/1125899906842624)), (60962427/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1955756865/67108864)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-1135281703/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-842307253359833/4503599627370496), (-743974433118043/4503599627370496)), (12640847/562949953421312), by norm_num⟩
  | 1 => ⟨((646420111/2147483648), (570955591/2147483648)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-520186517/2147483648), (-918917575/4294967296)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((1116277203/8589934592), (985960523/8589934592)), (143/8589934592), by norm_num⟩
  | 4 => ⟨((-449144713/8589934592), (-793421123/17179869184)), (117/17179869184), by norm_num⟩
  | 5 => ⟨((72287053/4294967296), (255392407/17179869184)), (77/34359738368), by norm_num⟩
  | 6 => ⟨((-310244063/68719476736), (-548050963/137438953472)), (21/34359738368), by norm_num⟩
  | 7 => ⟨((142662445/137438953472), (63003857/68719476736)), (79/549755813888), by norm_num⟩
  | 8 => ⟨((-918425391/4398046511104), (-811206369/4398046511104)), (129/4398046511104), by norm_num⟩
  | 9 => ⟨((656954953/17592186044416), (580260571/17592186044416)), (47/8796093022208), by norm_num⟩
  | 10 => ⟨((-845862567/140737488355328), (-373557345/70368744177664)), (123/140737488355328), by norm_num⟩
  | 11 => ⟨((990082389/1125899906842624), (874497969/1125899906842624)), (73/562949953421312), by norm_num⟩
  | 12 => ⟨((-531158711/4503599627370496), (-234575031/2251799813685248)), (159/9007199254740992), by norm_num⟩
  | 13 => ⟨((131517995/9007199254740992), (464657167/36028797018963968)), (5/2251799813685248), by norm_num⟩
  | 14 => ⟨((-483817251/288230376151711744), (-427335349/288230376151711744)), (149/576460752303423488), by norm_num⟩
  | 15 => ⟨((830585415/4611686018427387904), (366810513/2305843009213693952)), (65/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-167096957/9223372036854775808), (-295179373/18446744073709551616)), (107/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-3149851455833/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779820504530837/633825300114114700748351602688), (-3731908690843/633825300114114700748351602688)), (11571/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890924486715661/39614081257132168796771975168), (-4197863333085/39614081257132168796771975168)), (26041/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945386386604231/1237940039285380274899124224), (-4459596008649/2475880078570760549798248448)), (27675/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886219116838129/77371252455336267181195264), (-278680183841/9671406556917033397649408)), (55365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550722161959121/9671406556917033397649408), (-4179445123507/9671406556917033397649408)), (51921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259810490405213/604462909807314587353088), (-457032106081/75557863725914323419136)), (5681/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889450910964815/75557863725914323419136), (-2969998407033/37778931862957161709568)), (36941/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298782229361805/4722366482869645213696), (-1113438653997/1180591620717411303424)), (55439/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623154700703129/590295810358705651712), (-6121892730975/590295810358705651712)), (76271/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825604506031987/73786976294838206464), (-7649336116023/73786976294838206464)), (95405/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114065525495197/576460752303423488), (-1075167145351/1152921504606846976)), (26855/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798145576333529/576460752303423488), (-8596129712771/1152921504606846976)), (26883/288230376151711744), by norm_num⟩
  | 5 => ⟨((299147854911571/36028797018963968), (-7515755136187/144115188075855872)), (94217/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494640459626625/36028797018963968), (-2815479010765/9007199254740992)), (70789/18014398509481984), by norm_num⟩
  | 3 => ⟨((373247231641009/2251799813685248), (-7028445543067/4503599627370496)), (22177/1125899906842624), by norm_num⟩
  | 2 => ⟨((1117671512370139/2251799813685248), (-7013067814143/1125899906842624)), (89041/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113513958217271/1125899906842624), (-1310144815083/70368744177664)), (134395/562949953421312), by norm_num⟩
  | 0 => ⟨((1100956116695753/1125899906842624), (-20808553027065/562949953421312)), (136067/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100956116695753/1125899906842624), (-20808553027065/562949953421312)), (519054413915538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((537513317133019/562949953421312), (-81390196750189/1125899906842624)), (1104657/1125899906842624), by norm_num⟩
  | 2 => ⟨((255142107497959/281474976710656), (-155425235836415/1125899906842624)), (2269197/1125899906842624), by norm_num⟩
  | 3 => ⟨((451817657225993/562949953421312), (-281769432530653/1125899906842624)), (4740319/1125899906842624), by norm_num⟩
  | 4 => ⟨((654732062713575/1125899906842624), (-226145155728647/562949953421312)), (9981699/1125899906842624), by norm_num⟩
  | 5 => ⟨((398094975841155/2251799813685248), (-1052061437312799/2251799813685248)), (2453585/140737488355328), by norm_num⟩
  | 6 => ⟨((-842307253359833/4503599627370496), (-743974433118043/4503599627370496)), (12640847/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1135281703/33554432)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1263889539/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1919588650302303/9007199254740992), (30981722945569/4503599627370496)), (15136279/2251799813685248), by norm_num⟩
  | 1 => ⟨((-410013335/1073741824), (-26470087/2147483648)), (27/2147483648), by norm_num⟩
  | 2 => ⟨((1469290551/4294967296), (47428029/4294967296)), (25/2147483648), by norm_num⟩
  | 3 => ⟨((-1755076839/8589934592), (-7081635/1073741824)), (61/8589934592), by norm_num⟩
  | 4 => ⟨((1572337773/17179869184), (25377173/8589934592)), (7/2147483648), by norm_num⟩
  | 5 => ⟨((-563450219/17179869184), (-4546979/4294967296)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((1346089687/137438953472), (43451161/137438953472)), (13/34359738368), by norm_num⟩
  | 7 => ⟨((-1378210825/549755813888), (-44488017/549755813888)), (55/549755813888), by norm_num⟩
  | 8 => ⟨((308677787/549755813888), (39855913/2199023255552)), (51/2199023255552), by norm_num⟩
  | 9 => ⟨((-1966493681/17592186044416), (-3967345/1099511627776)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((704696735/35184372088832), (45494579/70368744177664)), (31/35184372088832), by norm_num⟩
  | 11 => ⟨((-1836577525/562949953421312), (-29641943/281474976710656)), (83/562949953421312), by norm_num⟩
  | 12 => ⟨((274225431/562949953421312), (276621/17592186044416)), (51/2251799813685248), by norm_num⟩
  | 13 => ⟨((-302366777/4503599627370496), (-39041047/18014398509481984)), (29/9007199254740992), by norm_num⟩
  | 14 => ⟨((619164041/72057594037927936), (19986333/72057594037927936)), (61/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1183352569/1152921504606846976), (-19099041/576460752303423488)), (15/288230376151711744), by norm_num⟩
  | 16 => ⟨((530070793/4611686018427387904), (4277611/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (2627069675/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792641092261/316912650057057350374175801344), (49787453391/633825300114114700748351602688)), (46103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890660331548409/39614081257132168796771975168), (28001621413/19807040628566084398385987584)), (25933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945246349976557/1237940039285380274899124224), (59494064655/2475880078570760549798248448)), (13777/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221519853211963/19342813113834066795298816), (14870878497/38685626227668133590597632)), (13777/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550460923540463/9671406556917033397649408), (55754586929/9671406556917033397649408)), (3229/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259582613024373/604462909807314587353088), (24387029555/302231454903657293676544)), (45207/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118067620857277/4722366482869645213696), (79236844037/75557863725914323419136)), (73461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298506653788179/4722366482869645213696), (59409262593/4722366482869645213696)), (6887/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622777663699295/590295810358705651712), (81657895975/590295810358705651712)), (75757/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825136026610023/73786976294838206464), (25506907647/18446744073709551616)), (94697/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912262619005823/4611686018427387904), (57359800735/4611686018427387904)), (13317/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797886406997635/576460752303423488), (114642798323/1152921504606846976)), (106537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196143300814697/144115188075855872), (50113057211/72057594037927936)), (46611/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493979117307113/36028797018963968), (150166676831/36028797018963968)), (34959/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492181168629895/9007199254740992), (187406869911/9007199254740992)), (87401/4503599627370496), by norm_num⟩
  | 2 => ⟨((558446024323207/1125899906842624), (373910868457/4503599627370496)), (43703/562949953421312), by norm_num⟩
  | 1 => ⟨((17381487475551/17592186044416), (558614564447/2251799813685248)), (524491/2251799813685248), by norm_num⟩
  | 0 => ⟨((2198077089771183/2251799813685248), (1108254742047/2251799813685248)), (131151/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2198077089771183/2251799813685248), (1108254742047/2251799813685248)), (500301362157726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2145635520078129/2251799813685248), (2163628705641/2251799813685248)), (2049387/2251799813685248), by norm_num⟩
  | 2 => ⟨((2044474413645755/2251799813685248), (515405340971/281474976710656)), (3909471/2251799813685248), by norm_num⟩
  | 3 => ⟨((464057528728641/562949953421312), (3743611757555/1125899906842624)), (3556681/1125899906842624), by norm_num⟩
  | 4 => ⟨((1530124551951571/2251799813685248), (3085978087701/562949953421312)), (11774845/2251799813685248), by norm_num⟩
  | 5 => ⟨((2079340053307341/4503599627370496), (16775668281269/2251799813685248)), (32262775/4503599627370496), by norm_num⟩
  | 6 => ⟨((1919588650302303/9007199254740992), (30981722945569/4503599627370496)), (15136279/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1263889539/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-1372625915/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-419435233165357/2251799813685248), (112131460442707/9007199254740992)), (137405989/9007199254740992), by norm_num⟩
  | 1 => ⟨((778373029/2147483648), (-52022397/2147483648)), (129/4294967296), by norm_num⟩
  | 2 => ⟨((-1514643977/4294967296), (50615455/2147483648)), (127/4294967296), by norm_num⟩
  | 3 => ⟨((15350839/67108864), (-65662085/4294967296)), (167/8589934592), by norm_num⟩
  | 4 => ⟨((-955883309/8589934592), (63886259/8589934592)), (165/17179869184), by norm_num⟩
  | 5 => ⟨((744025213/17179869184), (-3107923/1073741824)), (65/17179869184), by norm_num⟩
  | 6 => ⟨((-482602071/34359738368), (64509215/68719476736)), (171/137438953472), by norm_num⟩
  | 7 => ⟨((1073257449/274877906944), (-71730935/274877906944)), (3/8589934592), by norm_num⟩
  | 8 => ⟨((-1044231281/1099511627776), (69790977/1099511627776)), (95/1099511627776), by norm_num⟩
  | 9 => ⟨((1806204665/8796093022208), (-120717307/8796093022208)), (83/4398046511104), by norm_num⟩
  | 10 => ⟨((-351471199/8796093022208), (93962013/35184372088832)), (131/35184372088832), by norm_num⟩
  | 11 => ⟨((1989618541/281474976710656), (-66487867/140737488355328)), (47/70368744177664), by norm_num⟩
  | 12 => ⟨((-1290539637/1125899906842624), (86252943/1125899906842624)), (31/281474976710656), by norm_num⟩
  | 13 => ⟨((772699747/4503599627370496), (-103286447/9007199254740992)), (75/4503599627370496), by norm_num⟩
  | 14 => ⟨((-1718404891/72057594037927936), (57424613/36028797018963968)), (169/72057594037927936), by norm_num⟩
  | 15 => ⟨((891696405/288230376151711744), (-14899085/72057594037927936)), (89/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1735161085/4611686018427387904), (115969123/4611686018427387904)), (175/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (4005344700203/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444842034994851/158456325028528675187087900672), (2371608610807/316912650057057350374175801344)), (23167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890415386870799/39614081257132168796771975168), (5335294937879/39614081257132168796771975168)), (52141/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890231601301095/2475880078570760549798248448), (5667776095017/2475880078570760549798248448)), (55417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771896777024179/154742504910672534362390528), (5666679285169/154742504910672534362390528)), (13859/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550214244050183/9671406556917033397649408), (2655673219049/4835703278458516698824704)), (6499/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314841440052763/151115727451828646838272), (4646262706157/604462909807314587353088)), (22757/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472181914671559/18889465931478580854784), (943498955853/9444732965739290427392)), (36999/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298239295735409/4722366482869645213696), (5659081566697/4722366482869645213696)), (55533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622407364628381/590295810358705651712), (972266217875/73786976294838206464)), (76413/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824669134337555/73786976294838206464), (9718000823999/73786976294838206464)), (95599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911997232831315/4611686018427387904), (341448161959/288230376151711744)), (6729/576460752303423488), by norm_num⟩
  | 6 => ⟨((1595235153669571/1152921504606846976), (10918328438953/1152921504606846976)), (107807/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195665113075417/144115188075855872), (9544522287305/144115188075855872)), (23623/36028797018963968), by norm_num⟩
  | 4 => ⟨((186655800101973/4503599627370496), (7149375690365/18014398509481984)), (35515/9007199254740992), by norm_num⟩
  | 3 => ⟨((745619170359197/4503599627370496), (4460469770001/2251799813685248)), (44535/2251799813685248), by norm_num⟩
  | 2 => ⟨((557954489813609/1125899906842624), (1112158190209/140737488355328)), (178989/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110840542119841/1125899906842624), (26573400450117/1125899906842624)), (16913/70368744177664), by norm_num⟩
  | 0 => ⟨((1095492315371501/1125899906842624), (52673070984129/1125899906842624)), (137437/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095492315371501/1125899906842624), (52673070984129/1125899906842624)), (524280549169444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((132930218014317/140737488355328), (102501020098577/1125899906842624)), (140155/140737488355328), by norm_num⟩
  | 2 => ⟨((248779193690955/281474976710656), (96814879302043/562949953421312)), (2322235/1125899906842624), by norm_num⟩
  | 3 => ⟨((846225233885241/1125899906842624), (171137966802699/562949953421312)), (4903721/1125899906842624), by norm_num⟩
  | 4 => ⟨((132992357513003/281474976710656), (514508492643481/1125899906842624)), (10352747/1125899906842624), by norm_num⟩
  | 5 => ⟨((64916909208519/4503599627370496), (972387644496821/2251799813685248)), (38489821/2251799813685248), by norm_num⟩
  | 6 => ⟨((-419435233165357/2251799813685248), (112131460442707/9007199254740992)), (137405989/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1372625915/33554432)), (1/33554432), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-91676103/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1445175958432385/9007199254740992), (396426388551237/9007199254740992)), (117431249/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1432971441/4294967296), (-196539283/2147483648)), (119/4294967296), by norm_num⟩
  | 2 => ⟨((1489890171/4294967296), (204345975/2147483648)), (127/4294967296), by norm_num⟩
  | 3 => ⟨((-1032713171/4294967296), (-283283673/4294967296)), (45/2147483648), by norm_num⟩
  | 4 => ⟨((536866667/4294967296), (294535919/8589934592)), (3/268435456), by norm_num⟩
  | 5 => ⟨((-111638285/2147483648), (-122494045/8589934592)), (41/8589934592), by norm_num⟩
  | 6 => ⟨((154763525/8589934592), (42453201/8589934592)), (29/17179869184), by norm_num⟩
  | 7 => ⟨((-45974529/8589934592), (-403560913/274877906944)), (35/68719476736), by norm_num⟩
  | 8 => ⟨((1529621527/1099511627776), (52448833/137438953472)), (149/1099511627776), by norm_num⟩
  | 9 => ⟨((-1413670465/4398046511104), (-193892057/2199023255552)), (35/1099511627776), by norm_num⟩
  | 10 => ⟨((1175858037/17592186044416), (161274879/8796093022208)), (119/17592186044416), by norm_num⟩
  | 11 => ⟨((-889137473/70368744177664), (-121949703/35184372088832)), (23/17592186044416), by norm_num⟩
  | 12 => ⟨((1232606265/562949953421312), (338116371/562949953421312)), (65/281474976710656), by norm_num⟩
  | 13 => ⟨((-788656207/2251799813685248), (-108168189/1125899906842624)), (169/4503599627370496), by norm_num⟩
  | 14 => ⟨((937122559/18014398509481984), (257062201/18014398509481984)), (103/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1039302175/144115188075855872), (-8909097/4503599627370496)), (117/144115188075855872), by norm_num⟩
  | 16 => ⟨((1080584059/1152921504606846976), (148207571/576460752303423488)), (31/288230376151711744), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (174370670101/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779202432500149/633825300114114700748351602688), (12903397269/19807040628566084398385987584)), (92241/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118139355237269/2475880078570760549798248448), (464449135533/39614081257132168796771975168)), (51887/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472508802001447/618970019642690137449562112), (246693464807/1237940039285380274899124224)), (110263/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442925353482153/38685626227668133590597632), (246642699943/77371252455336267181195264)), (55133/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775016092590423/4835703278458516698824704), (115586804107/2417851639229258349412352)), (103379/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259207552109839/604462909807314587353088), (202223000727/302231454903657293676544)), (22615/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944236309670143/37778931862957161709568), (328511336667/37778931862957161709568)), (36751/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649024903809143/2361183241434822606848), (492590256019/4722366482869645213696)), (110259/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405537431749593/147573952589676412928), (338512258217/295147905179352825856)), (151615/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114021965359713/4611686018427387904), (422925123583/36893488147419103232)), (189533/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823643051832155/9223372036854775808), (950990103837/9223372036854775808)), (213245/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594891211546939/1152921504606846976), (475125691737/576460752303423488)), (106635/576460752303423488), by norm_num⟩
  | 5 => ⟨((597686277429903/72057594037927936), (830639669375/144115188075855872)), (11665/9007199254740992), by norm_num⟩
  | 4 => ⟨((746412154737613/18014398509481984), (311075210729/9007199254740992)), (280017/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490739950401429/9007199254740992), (1552477713999/9007199254740992)), (43765/1125899906842624), by norm_num⟩
  | 2 => ⟨((1115454262038451/2251799813685248), (1548138826033/2251799813685248)), (350271/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110267077581385/1125899906842624), (577847783745/281474976710656)), (262893/562949953421312), by norm_num⟩
  | 0 => ⟨((2189552839418969/2251799813685248), (9159388148685/2251799813685248)), (65819/70368744177664), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189552839418969/2251799813685248), (9159388148685/2251799813685248)), (251079559594607331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2128989314716461/2251799813685248), (8906193262123/1125899906842624)), (4113107/2251799813685248), by norm_num⟩
  | 2 => ⟨((1006367927006297/1125899906842624), (16840920027281/1125899906842624)), (7842639/2251799813685248), by norm_num⟩
  | 3 => ⟨((28102320135381/35184372088832), (60211966174725/2251799813685248)), (14254657/2251799813685248), by norm_num⟩
  | 4 => ⟨((1434919376744365/2251799813685248), (12023064850715/281474976710656)), (11766585/1125899906842624), by norm_num⟩
  | 5 => ⟨((1820536748996337/4503599627370496), (245167494798367/4503599627370496)), (8000651/562949953421312), by norm_num⟩
  | 6 => ⟨((1445175958432385/9007199254740992), (396426388551237/9007199254740992)), (117431249/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-91676103/2097152)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile017Terms0

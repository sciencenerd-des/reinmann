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
namespace Reinmann.XiBand97.Tile057Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨57,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78519/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78519/2560))
  have he : value ((69/80), (78519/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-22827593251/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-115227230790793/281474976710656), (-827104341870023/2251799813685248)), (6880127/2251799813685248), by norm_num⟩
  | 1 => ⟨((9749686297/34359738368), (4373970357/17179869184)), (75/34359738368), by norm_num⟩
  | 2 => ⟨((-422372973/4294967296), (-12127220883/137438953472)), (53/68719476736), by norm_num⟩
  | 3 => ⟨((12491376443/549755813888), (11207931951/549755813888)), (25/137438953472), by norm_num⟩
  | 4 => ⟨((-8658362363/2199023255552), (-121386663/34359738368)), (141/4398046511104), by norm_num⟩
  | 5 => ⟨((300075973/549755813888), (8615815497/17592186044416)), (5/1099511627776), by norm_num⟩
  | 6 => ⟨((-4437265379/70368744177664), (-15925408587/281474976710656)), (75/140737488355328), by norm_num⟩
  | 7 => ⟨((7030121113/1125899906842624), (3153900589/562949953421312)), (121/2251799813685248), by norm_num⟩
  | 8 => ⟨((-9745817257/18014398509481984), (-2186117301/4503599627370496)), (43/9007199254740992), by norm_num⟩
  | 9 => ⟨((375293653/9007199254740992), (1346934261/36028797018963968)), (27/72057594037927936), by norm_num⟩
  | 10 => ⟨((-6659423679/2305843009213693952), (-11950383173/4611686018427387904)), (61/2305843009213693952), by norm_num⟩
  | 11 => ⟨((13428249447/73786976294838206464), (6024272293/36893488147419103232)), (125/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-12410337659/1180591620717411303424), (-11135219613/1180591620717411303424)), (117/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((330853483/590295810358705651712), (9499502867/18889465931478580854784)), (51/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-16773863053/604462909807314587353088), (-15050408295/604462909807314587353088)), (41/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((12401872941/9671406556917033397649408), (11127624615/9671406556917033397649408)), (31/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-8596323263/154742504910672534362390528), (-15426163257/309485009821345068724781056)), (87/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-1569840474993/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890520516855721/316912650057057350374175801344), (-3724705063439/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892297446007793/39614081257132168796771975168), (-523756235345/4951760157141521099596496896)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1892231396114453/2475880078570760549798248448), (-4451654174749/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773896691778155/154742504910672534362390528), (-4451345974335/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552089291194567/9671406556917033397649408), (-2086404628633/4835703278458516698824704)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261006553104161/604462909807314587353088), (-3650880359453/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891394183697105/75557863725914323419136), (-1483016439545/18889465931478580854784)), (4619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300239395589825/4722366482869645213696), (-4448511033893/4722366482869645213696)), (1733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625157835160445/590295810358705651712), (-1528956843529/147573952589676412928)), (149/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1828107719422879/73786976294838206464), (-7643470248683/73786976294838206464)), (5963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456965888098493/2305843009213693952), (-8597095661703/9223372036854775808)), (3357/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599105081411999/1152921504606846976), (-8594832712597/1152921504606846976)), (6721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599526118098615/72057594037927936), (-7517929386767/144115188075855872)), (5889/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498328933744625/36028797018963968), (-88060836479/281474976710656)), (8849/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497594686377169/9007199254740992), (-3520194346685/2251799813685248)), (11089/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122269984855837/2251799813685248), (-14067304420209/2251799813685248)), (5565/1125899906842624), by norm_num⟩
  | 1 => ⟨((560196657935921/562949953421312), (-5266785127287/281474976710656)), (8399/562949953421312), by norm_num⟩
  | 0 => ⟨((1114640635257837/1125899906842624), (-10499554208771/281474976710656)), (34011/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114640635257837/1125899906842624), (-10499554208771/281474976710656)), (129741672996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((550963672707757/562949953421312), (-83156449002705/1125899906842624)), (8735/140737488355328), by norm_num⟩
  | 2 => ⟨((1072323456309247/1125899906842624), (-81385889231217/562949953421312)), (147107/1125899906842624), by norm_num⟩
  | 3 => ⟨((249441121777313/281474976710656), (-310052421195977/1125899906842624)), (322749/1125899906842624), by norm_num⟩
  | 4 => ⟨((399414487194117/562949953421312), (-274766249762935/562949953421312)), (749795/1125899906842624), by norm_num⟩
  | 5 => ⟨((597107718446579/2251799813685248), (-1559579072069729/2251799813685248)), (3591775/2251799813685248), by norm_num⟩
  | 6 => ⟨((-115227230790793/281474976710656), (-827104341870023/2251799813685248)), (6880127/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-22827593251/1073741824)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-18090439641/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-568616272770527/2251799813685248), (-82802391444191/281474976710656)), (9731691/2251799813685248), by norm_num⟩
  | 1 => ⟨((9531995007/34359738368), (5552229295/17179869184)), (165/34359738368), by norm_num⟩
  | 2 => ⟨((-5235983425/34359738368), (-6099747333/34359738368)), (183/68719476736), by norm_num⟩
  | 3 => ⟨((958719289/17179869184), (8935009837/137438953472)), (271/274877906944), by norm_num⟩
  | 4 => ⟨((-4213043169/274877906944), (-4908055803/274877906944)), (151/549755813888), by norm_num⟩
  | 5 => ⟨((7405601597/2199023255552), (17254561339/4398046511104)), (67/1099511627776), by norm_num⟩
  | 6 => ⟨((-10847846559/17592186044416), (-6318691041/8796093022208)), (199/17592186044416), by norm_num⟩
  | 7 => ⟨((3405022153/35184372088832), (495842259/4398046511104)), (253/140737488355328), by norm_num⟩
  | 8 => ⟨((-7481598361/562949953421312), (-17431628767/1125899906842624)), (281/1125899906842624), by norm_num⟩
  | 9 => ⟨((14612223819/9007199254740992), (17022756955/9007199254740992)), (277/9007199254740992), by norm_num⟩
  | 10 => ⟨((-6421267461/36028797018963968), (-7480563991/36028797018963968)), (123/36028797018963968), by norm_num⟩
  | 11 => ⟨((5130533339/288230376151711744), (2988450737/144115188075855872)), (199/576460752303423488), by norm_num⟩
  | 12 => ⟨((-3757644649/2305843009213693952), (-4377531605/2305843009213693952)), (147/4611686018427387904), by norm_num⟩
  | 13 => ⟨((10161709755/73786976294838206464), (5919027711/36893488147419103232)), (201/73786976294838206464), by norm_num⟩
  | 14 => ⟨((-3189651203/295147905179352825856), (-14863352183/1180591620717411303424)), (255/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((14951210701/18889465931478580854784), (17417665449/18889465931478580854784)), (151/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((-8212791903/151115727451828646838272), (-9567630651/151115727451828646838272)), (21/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-2970140978599/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780501542746233/633825300114114700748351602688), (-3521545602933/633825300114114700748351602688)), (5785/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891690614800651/39614081257132168796771975168), (-495173519479/4951760157141521099596496896)), (3255/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945793373585053/1237940039285380274899124224), (-2104283053625/1237940039285380274899124224)), (3459/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886626082879697/77371252455336267181195264), (-4208106100125/154742504910672534362390528)), (865/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551485178702699/9671406556917033397649408), (-986152661637/2417851639229258349412352)), (6489/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260478085372033/604462909807314587353088), (-3451045420593/604462909807314587353088)), (355/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1890535668792549/75557863725914323419136), (-5607031975503/75557863725914323419136)), (9233/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299595724027363/4722366482869645213696), (-2102235799191/2361183241434822606848)), (433/295147905179352825856), by norm_num⟩
  | 9 => ⟨((812136567850903/295147905179352825856), (-2889922142933/295147905179352825856)), (9531/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913501184419601/36893488147419103232), (-451428038077/4611686018427387904)), (11921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913310376832375/4611686018427387904), (-8123013337135/9223372036854775808)), (6711/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798931592165635/576460752303423488), (-1014955990607/144115188075855872)), (13435/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197966591706199/144115188075855872), (-7100904162337/144115188075855872)), (11771/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496702500660455/36028797018963968), (-5321888251937/18014398509481984)), (17685/36028797018963968), by norm_num⟩
  | 3 => ⟨((46736412814581/281474976710656), (-6645723338869/4503599627370496)), (22159/9007199254740992), by norm_num⟩
  | 2 => ⟨((560122934185159/1125899906842624), (-13271517016071/2251799813685248)), (22237/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117370583394261/1125899906842624), (-19857386171359/1125899906842624)), (2097/70368744177664), by norm_num⟩
  | 0 => ⟨((1108649193711789/1125899906842624), (-39514826687301/1125899906842624)), (67889/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108649193711789/1125899906842624), (-39514826687301/1125899906842624)), (258975986960982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((545137985059473/562949953421312), (-38909391927555/562949953421312)), (4327/35184372088832), by norm_num⟩
  | 2 => ⟨((1050400591305341/1125899906842624), (-37678282743195/281474976710656)), (287307/1125899906842624), by norm_num⟩
  | 3 => ⟨((479894770307517/562949953421312), (-140606781232655/562949953421312)), (613001/1125899906842624), by norm_num⟩
  | 4 => ⟨((5843345908249/8796093022208), (-239724538827077/562949953421312)), (337835/281474976710656), by norm_num⟩
  | 5 => ⟨((585407643943923/2251799813685248), (-1274014178363431/2251799813685248)), (5892643/2251799813685248), by norm_num⟩
  | 6 => ⟨((-568616272770527/2251799813685248), (-82802391444191/281474976710656)), (9731691/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-18090439641/536870912)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-22827593251/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((147123690533037/4503599627370496), (169295587129041/562949953421312)), (13053321/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3112132913/68719476736), (-7162277765/17179869184)), (139/34359738368), by norm_num⟩
  | 2 => ⟨((1078583077/34359738368), (19858050557/68719476736)), (97/34359738368), by norm_num⟩
  | 3 => ⟨((-996822425/68719476736), (-9176367837/68719476736)), (181/137438953472), by norm_num⟩
  | 4 => ⟨((1381889307/274877906944), (3180286747/68719476736)), (253/549755813888), by norm_num⟩
  | 5 => ⟨((-1532564283/1099511627776), (-28216406939/2199023255552)), (283/2199023255552), by norm_num⟩
  | 6 => ⟨((1416390149/4398046511104), (26077497221/8796093022208)), (33/1099511627776), by norm_num⟩
  | 7 => ⟨((-280504811/4398046511104), (-2582220525/4398046511104)), (211/35184372088832), by norm_num⟩
  | 8 => ⟨((1555448951/140737488355328), (3579717753/35184372088832)), (295/281474976710656), by norm_num⟩
  | 9 => ⟨((-958360049/562949953421312), (-8822297841/562949953421312)), (23/140737488355328), by norm_num⟩
  | 10 => ⟨((2125710611/9007199254740992), (19568482799/9007199254740992)), (103/4503599627370496), by norm_num⟩
  | 11 => ⟨((-1071585685/36028797018963968), (-9864609949/36028797018963968)), (105/36028797018963968), by norm_num⟩
  | 12 => ⟨((1980710923/576460752303423488), (18233670863/576460752303423488)), (49/144115188075855872), by norm_num⟩
  | 13 => ⟨((-1689752851/4611686018427387904), (-486100675/144115188075855872)), (169/4611686018427387904), by norm_num⟩
  | 14 => ⟨((1338568485/36893488147419103232), (24644703989/73786976294838206464)), (135/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-1979359939/590295810358705651712), (-18221234225/590295810358705651712)), (201/590295810358705651712), by norm_num⟩
  | 16 => ⟨((1371987761/4722366482869645213696), (25259994259/9444732965739290427392)), (281/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (952594241957/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111257643621137/39614081257132168796771975168), (282245264789/79228162514264337593543950336)), (5777/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945632120026865/19807040628566084398385987584), (1269966606843/19807040628566084398385987584)), (1625/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945567030924319/1237940039285380274899124224), (1349174659639/1237940039285380274899124224)), (1727/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886399930225955/77371252455336267181195264), (337247301103/19342813113834066795298816)), (1727/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551061546149583/9671406556917033397649408), (632240175579/2417851639229258349412352)), (3239/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630053905228529/302231454903657293676544), (2212446599503/604462909807314587353088)), (2835/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944967364263645/37778931862957161709568), (3594487033027/75557863725914323419136)), (9215/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299145680520693/4722366482869645213696), (2695219007027/4722366482869645213696)), (3457/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623655400716801/590295810358705651712), (926219028201/147573952589676412928)), (9509/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228278976454935/9223372036854775808), (4629520393957/73786976294838206464)), (11891/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912878045747435/4611686018427387904), (1301511407631/2305843009213693952)), (1673/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1597001288746333/1152921504606846976), (5203340311767/1152921504606846976)), (837/72057594037927936), by norm_num⟩
  | 5 => ⟨((598607771524809/72057594037927936), (4549880248217/144115188075855872)), (733/9007199254740992), by norm_num⟩
  | 4 => ⟨((1495582141562933/36028797018963968), (1704684430571/9007199254740992)), (8805/18014398509481984), by norm_num⟩
  | 3 => ⟨((747087810911605/4503599627370496), (2128195729397/2251799813685248)), (22047/9007199254740992), by norm_num⟩
  | 2 => ⟨((279718135924161/562949953421312), (1062104359999/281474976710656)), (22097/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115351159393147/1125899906842624), (1588177515943/140737488355328)), (16635/562949953421312), by norm_num⟩
  | 0 => ⟨((276193005347791/281474976710656), (25251739276785/1125899906842624)), (16761/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276193005347791/281474976710656), (25251739276785/1125899906842624)), (63938141942882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1083474260454601/1125899906842624), (774308812747/17592186044416)), (33645/281474976710656), by norm_num⟩
  | 2 => ⟨((1040466112663245/1125899906842624), (95376852670431/1125899906842624)), (135433/562949953421312), by norm_num⟩
  | 3 => ⟨((953435541695355/1125899906842624), (176279227901081/1125899906842624)), (546517/1125899906842624), by norm_num⟩
  | 4 => ⟨((1559579072069741/2251799813685248), (597107718446587/2251799813685248)), (548369/562949953421312), by norm_num⟩
  | 5 => ⟨((230454461581589/562949953421312), (103388042733755/281474976710656)), (2100827/1125899906842624), by norm_num⟩
  | 6 => ⟨((147123690533037/4503599627370496), (169295587129041/562949953421312)), (13053321/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-22827593251/536870912)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-26502015053/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((697141740557037/4503599627370496), (440730321306025/2251799813685248)), (4222101/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2140057273/8589934592), (-10823487675/34359738368)), (105/34359738368), by norm_num⟩
  | 2 => ⟨((1722144655/8589934592), (17419731409/68719476736)), (171/68719476736), by norm_num⟩
  | 3 => ⟨((-7391159729/68719476736), (-18690650769/137438953472)), (93/68719476736), by norm_num⟩
  | 4 => ⟨((11895612685/274877906944), (7520360489/137438953472)), (19/34359738368), by norm_num⟩
  | 5 => ⟨((-7658100019/549755813888), (-9682842629/549755813888)), (25/137438953472), by norm_num⟩
  | 6 => ⟨((4108412169/1099511627776), (10389289351/2199023255552)), (109/2199023255552), by norm_num⟩
  | 7 => ⟨((-15113678411/17592186044416), (-9554809237/8796093022208)), (203/17592186044416), by norm_num⟩
  | 8 => ⟨((12162263515/70368744177664), (1922234029/8796093022208)), (165/70368744177664), by norm_num⟩
  | 9 => ⟨((-4349868445/140737488355328), (-10999880259/281474976710656)), (15/35184372088832), by norm_num⟩
  | 10 => ⟨((11201349103/2251799813685248), (14162899457/2251799813685248)), (39/562949953421312), by norm_num⟩
  | 11 => ⟨((-13111182485/18014398509481984), (-8288839031/9007199254740992)), (185/18014398509481984), by norm_num⟩
  | 12 => ⟨((879234757/9007199254740992), (8893581191/72057594037927936)), (25/18014398509481984), by norm_num⟩
  | 13 => ⟨((-1741629233/144115188075855872), (-8808410305/576460752303423488)), (25/144115188075855872), by norm_num⟩
  | 14 => ⟨((12813915963/9223372036854775808), (16201816563/9223372036854775808)), (93/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-10999041151/73786976294838206464), (-13907102841/73786976294838206464)), (81/36893488147419103232), by norm_num⟩
  | 16 => ⟨((4425568457/295147905179352825856), (5595654641/295147905179352825856)), (33/147573952589676412928), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (1174477225853/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779826908560873/633825300114114700748351602688), (695753724871/316912650057057350374175801344)), (1443/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890932065457141/39614081257132168796771975168), (1565252429305/39614081257132168796771975168)), (3247/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890781297694609/2475880078570760549798248448), (207855632927/309485009821345068724781056)), (1725/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772447289013479/154742504910672534362390528), (1662580015175/154742504910672534362390528)), (6901/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550731215126019/9671406556917033397649408), (779193600965/4835703278458516698824704)), (6471/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259818975443519/604462909807314587353088), (2662709565/1180591620717411303424)), (5663/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944732877585605/37778931862957161709568), (2214846660299/75557863725914323419136)), (9203/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298794285957741/4722366482869645213696), (830336691313/2361183241434822606848)), (6903/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623172778035369/590295810358705651712), (570669002783/147573952589676412928)), (4747/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456407337519685/18446744073709551616), (1426110291099/36893488147419103232)), (5935/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825079444558539/9223372036854775808), (3207202716437/9223372036854775808)), (6679/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49885188861173/36028797018963968), (801317975127/288230376151711744)), (13363/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598313139446169/72057594037927936), (2802442095009/144115188075855872)), (11699/144115188075855872), by norm_num⟩
  | 4 => ⟨((373675348034343/9007199254740992), (4199324879809/36028797018963968)), (2195/4503599627370496), by norm_num⟩
  | 3 => ⟨((1493080183065543/9007199254740992), (5241571724715/9007199254740992)), (10985/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235570668405339/4503599627370496), (5230210319191/2251799813685248)), (44001/4503599627370496), by norm_num⟩
  | 1 => ⟨((1113740856174149/1125899906842624), (15633929918325/2251799813685248)), (16539/562949953421312), by norm_num⟩
  | 0 => ⟨((2203266173512439/2251799813685248), (7760422680703/562949953421312)), (132935/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203266173512439/2251799813685248), (7760422680703/562949953421312)), (507106789595793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155350673396767/2251799813685248), (30372640908197/1125899906842624)), (131903/1125899906842624), by norm_num⟩
  | 2 => ⟨((1030696980219613/1125899906842624), (116286877077557/2251799813685248)), (519247/2251799813685248), by norm_num⟩
  | 3 => ⟨((1881083032608751/2251799813685248), (53226993054437/562949953421312)), (125539/281474976710656), by norm_num⟩
  | 4 => ⟨((96954210519325/140737488355328), (177856651204929/1125899906842624)), (933929/1125899906842624), by norm_num⟩
  | 5 => ⟨((1012478320947363/2251799813685248), (490102570528985/2251799813685248)), (3163665/2251799813685248), by norm_num⟩
  | 6 => ⟨((697141740557037/4503599627370496), (440730321306025/2251799813685248)), (4222101/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-26502015053/536870912)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-29504236267/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-10537842084843/2251799813685248), (480031464928545/2251799813685248)), (9635795/4503599627370496), by norm_num⟩
  | 1 => ⟨((576210887/68719476736), (-6562049277/17179869184)), (265/68719476736), by norm_num⟩
  | 2 => ⟨((-516215657/68719476736), (5878806965/17179869184)), (15/4294967296), by norm_num⟩
  | 3 => ⟨((616622861/137438953472), (-28089088127/137438953472)), (289/137438953472), by norm_num⟩
  | 4 => ⟨((-552419925/274877906944), (25164444817/274877906944)), (65/68719476736), by norm_num⟩
  | 5 => ⟨((395921453/549755813888), (-4508863229/137438953472)), (47/137438953472), by norm_num⟩
  | 6 => ⟨((-472930675/2199023255552), (21543462363/2199023255552)), (113/1099511627776), by norm_num⟩
  | 7 => ⟨((484216009/8796093022208), (-11028772197/4398046511104)), (233/8796093022208), by norm_num⟩
  | 8 => ⟨((-216899655/17592186044416), (9880453509/17592186044416)), (105/17592186044416), by norm_num⟩
  | 9 => ⟨((86362669/35184372088832), (-31472704241/281474976710656)), (337/281474976710656), by norm_num⟩
  | 10 => ⟨((-15474113/35184372088832), (22556606339/1125899906842624)), (243/1125899906842624), by norm_num⟩
  | 11 => ⟨((645257041/9007199254740992), (-14696732001/4503599627370496)), (319/9007199254740992), by norm_num⟩
  | 12 => ⟨((-96345451/9007199254740992), (17555339153/36028797018963968)), (3/562949953421312), by norm_num⟩
  | 13 => ⟨((53116269/36028797018963968), (-19356889331/288230376151711744)), (213/288230376151711744), by norm_num⟩
  | 14 => ⟨((-435070071/2305843009213693952), (19818794145/2305843009213693952)), (55/576460752303423488), by norm_num⟩
  | 15 => ⟨((415755157/18446744073709551616), (-18938939775/18446744073709551616)), (53/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-93116655/36893488147419103232), (4241753085/36893488147419103232)), (3/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (259341056761/1267650600228229401496703205376)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779582056444827/633825300114114700748351602688), (1228738896683/316912650057057350374175801344)), (5779/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890656515587113/39614081257132168796771975168), (2764280283959/39614081257132168796771975168)), (3251/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118155525492073/154742504910672534362390528), (2936584172019/2475880078570760549798248448)), (6909/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886077133220107/77371252455336267181195264), (2936062658447/154742504910672534362390528)), (3455/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550456365499025/9671406556917033397649408), (2752004719155/9671406556917033397649408)), (405/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259578341150119/604462909807314587353088), (1203725100869/302231454903657293676544)), (5671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944537230257461/37778931862957161709568), (3911068166911/75557863725914323419136)), (4609/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649250292114217/2361183241434822606848), (2932392718831/4722366482869645213696)), (1729/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811384281793459/295147905179352825856), (2015282104539/295147905179352825856)), (9513/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825123520821767/73786976294838206464), (2517996129583/36893488147419103232)), (1487/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824509616070465/9223372036854775808), (5662449497147/9223372036854775808)), (6695/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797877626728675/576460752303423488), (1414662219897/288230376151711744)), (13399/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196125757946367/144115188075855872), (2473522155015/72057594037927936)), (11735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493948457008943/36028797018963968), (1853006283523/9007199254740992)), (17623/36028797018963968), by norm_num⟩
  | 3 => ⟨((746067628768795/4503599627370496), (4625048331569/4503599627370496)), (22065/9007199254740992), by norm_num⟩
  | 2 => ⟨((558417399227323/1125899906842624), (9227719683491/2251799813685248)), (2765/281474976710656), by norm_num⟩
  | 1 => ⟨((556150556641565/562949953421312), (13785725120175/1125899906842624)), (8329/281474976710656), by norm_num⟩
  | 0 => ⟨((137337295008375/140737488355328), (13674280488073/562949953421312)), (33591/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137337295008375/140737488355328), (13674280488073/562949953421312)), (128139497997093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2142979380839537/2251799813685248), (106751297915807/2251799813685248)), (67191/562949953421312), by norm_num⟩
  | 2 => ⟨((508589258163183/562949953421312), (50796218411849/562949953421312)), (537035/2251799813685248), by norm_num⟩
  | 3 => ⟨((1819577574579743/2251799813685248), (91782265484061/562949953421312)), (533635/1125899906842624), by norm_num⟩
  | 4 => ⟨((1410462325510815/2251799813685248), (593320777465045/2251799813685248)), (1036419/1125899906842624), by norm_num⟩
  | 5 => ⟨((181785078846991/562949953421312), (743277975663077/2251799813685248)), (1844533/1125899906842624), by norm_num⟩
  | 6 => ⟨((-10537842084843/2251799813685248), (480031464928545/2251799813685248)), (9635795/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-29504236267/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-32042578135/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1681450438883353/9007199254740992), (-5303101191481/4503599627370496)), (16836813/9007199254740992), by norm_num⟩
  | 1 => ⟨((6240752171/17179869184), (78730457/34359738368)), (63/17179869184), by norm_num⟩
  | 2 => ⟨((-24287885975/68719476736), (-153202395/68719476736)), (247/68719476736), by norm_num⟩
  | 3 => ⟨((7877007303/34359738368), (198745397/137438953472)), (161/68719476736), by norm_num⟩
  | 4 => ⟨((-30655896911/274877906944), (-193370343/274877906944)), (79/68719476736), by norm_num⟩
  | 5 => ⟨((23861448371/549755813888), (150512525/549755813888)), (31/68719476736), by norm_num⟩
  | 6 => ⟨((-15477411519/1099511627776), (-48813975/549755813888)), (323/2199023255552), by norm_num⟩
  | 7 => ⟨((8605043473/2199023255552), (27139317/1099511627776)), (181/4398046511104), by norm_num⟩
  | 8 => ⟨((-33489282855/35184372088832), (-105621345/17592186044416)), (177/17592186044416), by norm_num⟩
  | 9 => ⟨((14481585643/70368744177664), (45673255/35184372088832)), (77/35184372088832), by norm_num⟩
  | 10 => ⟨((-11271945791/281474976710656), (-142201681/562949953421312)), (241/562949953421312), by norm_num⟩
  | 11 => ⟨((31904281767/4503599627370496), (201244869/4503599627370496)), (343/4503599627370496), by norm_num⟩
  | 12 => ⟨((-20694288563/18014398509481984), (-130534811/18014398509481984)), (7/562949953421312), by norm_num⟩
  | 13 => ⟨((12390531121/72057594037927936), (156313239/144115188075855872)), (135/72057594037927936), by norm_num⟩
  | 14 => ⟨((-13777634435/576460752303423488), (-21726537/144115188075855872)), (151/576460752303423488), by norm_num⟩
  | 15 => ⟨((28597374589/9223372036854775808), (180385659/9223372036854775808)), (315/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-27823960725/73786976294838206464), (-87753571/36893488147419103232)), (77/18446744073709551616), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-2042029363209/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444841915650585/158456325028528675187087900672), (-2418216050677/316912650057057350374175801344)), (5793/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890414822333313/39614081257132168796771975168), (-5440144013947/39614081257132168796771975168)), (6519/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945115483172409/1237940039285380274899124224), (-5779158908669/2475880078570760549798248448)), (6929/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771896102558075/154742504910672534362390528), (-5778040328865/154742504910672534362390528)), (6931/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550213569780861/9671406556917033397649408), (-5415724272045/9671406556917033397649408)), (1625/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259365128292573/604462909807314587353088), (-4737570150657/604462909807314587353088)), (5691/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29511352394481/1180591620717411303424), (-7696322785471/75557863725914323419136)), (2313/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162279799744689/590295810358705651712), (-5770291861113/4722366482869645213696)), (217/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1622406018646763/590295810358705651712), (-3965490994405/295147905179352825856)), (4777/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824667284726079/73786976294838206464), (-9908973159085/73786976294838206464)), (11953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227999019414731/1152921504606846976), (-11141057046745/9223372036854775808)), (6731/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398808139206749/288230376151711744), (-1391610502913/144115188075855872)), (1685/144115188075855872), by norm_num⟩
  | 5 => ⟨((37364453721927/4503599627370496), (-4866038873837/72057594037927936)), (1477/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493241867816161/36028797018963968), (-7289861159811/18014398509481984)), (4441/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491231554127719/9007199254740992), (-18192456798003/9007199254740992)), (22277/9007199254740992), by norm_num⟩
  | 2 => ⟨((557950259490205/1125899906842624), (-9072075410367/1125899906842624)), (22385/2251799813685248), by norm_num⟩
  | 1 => ⟨((277705922152459/281474976710656), (-27095421343985/1125899906842624)), (4231/140737488355328), by norm_num⟩
  | 0 => ⟨((1095442093840625/1125899906842624), (-6713424374119/140737488355328)), (68783/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095442093840625/1125899906842624), (-6713424374119/140737488355328)), (262386326316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531623144031547/562949953421312), (-104509008071227/1125899906842624)), (17551/140737488355328), by norm_num⟩
  | 2 => ⟨((994378389684339/1125899906842624), (-197386666835243/1125899906842624)), (36407/140737488355328), by norm_num⟩
  | 3 => ⟨((52725983891549/70368744177664), (-174329027580445/562949953421312)), (308295/562949953421312), by norm_num⟩
  | 4 => ⟨((524136362017547/1125899906842624), (-522485919420657/1125899906842624)), (2611757/2251799813685248), by norm_num⟩
  | 5 => ⟨((6136922067909/4503599627370496), (-972924386426173/2251799813685248)), (4855713/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1681450438883353/9007199254740992), (-5303101191481/4503599627370496)), (16836813/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-32042578135/536870912)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-481443911/268435456), (-8560347469/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((218620605459345/2251799813685248), (-1216950263157815/9007199254740992)), (11615789/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3468389655/17179869184), (19306769801/68719476736)), (371/68719476736), by norm_num⟩
  | 2 => ⟨((7212313531/34359738368), (-5018412395/17179869184)), (195/34359738368), by norm_num⟩
  | 3 => ⟨((-9998389579/68719476736), (6956996805/34359738368)), (17/4294967296), by norm_num⟩
  | 4 => ⟨((1299441665/17179869184), (-7233334081/68719476736)), (285/137438953472), by norm_num⟩
  | 5 => ⟨((-8646761533/274877906944), (6016518149/137438953472)), (15/17179869184), by norm_num⟩
  | 6 => ⟨((11986956755/1099511627776), (-16681330367/1099511627776)), (335/1099511627776), by norm_num⟩
  | 7 => ⟨((-1780441131/549755813888), (19821629335/4398046511104)), (401/4398046511104), by norm_num⟩
  | 8 => ⟨((7404646501/8796093022208), (-5152239933/4398046511104)), (105/4398046511104), by norm_num⟩
  | 9 => ⟨((-13686692921/70368744177664), (9523361555/35184372088832)), (391/70368744177664), by norm_num⟩
  | 10 => ⟨((11384271131/281474976710656), (-15842618907/281474976710656)), (41/35184372088832), by norm_num⟩
  | 11 => ⟨((-8608336841/1125899906842624), (5989781797/562949953421312)), (125/562949953421312), by norm_num⟩
  | 12 => ⟨((11933688821/9007199254740992), (-16607201459/9007199254740992)), (349/9007199254740992), by norm_num⟩
  | 13 => ⟨((-238609695/1125899906842624), (10625755263/36028797018963968)), (225/36028797018963968), by norm_num⟩
  | 14 => ⟨((9072912677/288230376151711744), (-1578259779/36028797018963968)), (269/288230376151711744), by norm_num⟩
  | 15 => ⟨((-5031091073/1152921504606846976), (14002768845/2305843009213693952)), (301/2305843009213693952), by norm_num⟩
  | 16 => ⟨((10461859777/18446744073709551616), (-14558969617/18446744073709551616)), (79/4611686018427387904), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395409877308005/2535301200456458802993406410752), (-617246232429/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779201381169129/633825300114114700748351602688), (-1461635417517/633825300114114700748351602688)), (1443/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890228440864553/39614081257132168796771975168), (-411019968603/9903520314283042199192993792)), (3247/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945016905017023/1237940039285380274899124224), (-873257592497/1237940039285380274899124224)), (13801/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771699928990955/154742504910672534362390528), (-873077820841/77371252455336267181195264)), (6901/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193753837587661/1208925819614629174706176), (-1636638994429/9671406556917033397649408)), (6471/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314801540224217/151115727451828646838272), (-1431677307487/604462909807314587353088)), (11325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236058773211317/9444732965739290427392), (-1162879976649/37778931862957161709568)), (9203/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162255978898711/590295810358705651712), (-435923494945/1180591620717411303424)), (13807/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622146763950501/590295810358705651712), (-2396562422201/590295810358705651712)), (18989/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824347374155201/73786976294838206464), (-2994178572839/73786976294838206464)), (23743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911818983107733/4611686018427387904), (-841588994777/2305843009213693952)), (835/288230376151711744), by norm_num⟩
  | 6 => ⟨((1594885495564137/1152921504606846976), (-3363739149153/1152921504606846976)), (26731/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195366845540933/144115188075855872), (-1470165157335/72057594037927936)), (11701/72057594037927936), by norm_num⟩
  | 4 => ⟨((746407166572073/18014398509481984), (-4404618817427/36028797018963968)), (35127/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490725015815889/9007199254740992), (-5495503373369/9007199254740992)), (2747/562949953421312), by norm_num⟩
  | 2 => ⟨((2230871292107269/4503599627370496), (-10960252220527/4503599627370496)), (44017/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220460003922741/2251799813685248), (-16363687420145/2251799813685248)), (66189/1125899906842624), by norm_num⟩
  | 0 => ⟨((2189331943690817/2251799813685248), (-16210890568059/1125899906842624)), (33259/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189331943690817/2251799813685248), (-16210890568059/1125899906842624)), (126873017431163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2128130199962263/2251799813685248), (-985073704727/35184372088832)), (525045/2251799813685248), by norm_num⟩
  | 2 => ⟨((502371867620797/562949953421312), (-119164559476885/2251799813685248)), (1021819/2251799813685248), by norm_num⟩
  | 3 => ⟨((55841993554151/70368744177664), (-212682928330609/2251799813685248)), (1931875/2251799813685248), by norm_num⟩
  | 4 => ⟨((698981782222719/1125899906842624), (-337554374508381/2251799813685248)), (857765/562949953421312), by norm_num⟩
  | 5 => ⟨((408641825215217/1125899906842624), (-104780343642005/562949953421312)), (5288807/2251799813685248), by norm_num⟩
  | 6 => ⟨((218620605459345/2251799813685248), (-1216950263157815/9007199254740992)), (11615789/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-481443911/268435456), (-8560347469/134217728)), (1/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile057Terms0

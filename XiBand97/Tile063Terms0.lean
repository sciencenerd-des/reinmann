/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile063Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨63,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80667/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80667/2560))
  have he : value ((69/80), (80667/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-2567700857/4294967296), (-46904149689/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-76539695383011/140737488355328), (-92356024823333/1125899906842624)), (1592929/2251799813685248), by norm_num⟩
  | 1 => ⟨((51809837945/137438953472), (15628983939/274877906944)), (137/274877906944), by norm_num⟩
  | 2 => ⟨((-35911843097/274877906944), (-1354148269/68719476736)), (97/549755813888), by norm_num⟩
  | 3 => ⟨((66379180777/2199023255552), (10011989917/2199023255552)), (91/2199023255552), by norm_num⟩
  | 4 => ⟨((-92021084007/17592186044416), (-13879565165/17592186044416)), (129/17592186044416), by norm_num⟩
  | 5 => ⟨((51027323945/70368744177664), (7696465169/70368744177664)), (145/140737488355328), by norm_num⟩
  | 6 => ⟨((-47159260965/562949953421312), (-444565261/35184372088832)), (17/140737488355328), by norm_num⟩
  | 7 => ⟨((74716134343/9007199254740992), (11269454893/9007199254740992)), (109/9007199254740992), by norm_num⟩
  | 8 => ⟨((-25894638931/36028797018963968), (-15622781771/144115188075855872)), (153/144115188075855872), by norm_num⟩
  | 9 => ⟨((63817941215/1152921504606846976), (9625677455/1152921504606846976)), (3/36028797018963968), by norm_num⟩
  | 10 => ⟨((-17694090409/4611686018427387904), (-5337608951/9223372036854775808)), (109/18446744073709551616), by norm_num⟩
  | 11 => ⟨((35678862195/147573952589676412928), (10762905005/295147905179352825856)), (7/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-65948540629/4722366482869645213696), (-9947036345/4722366482869645213696)), (105/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((14065244615/18889465931478580854784), (16971717409/151115727451828646838272)), (91/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-89136316789/2417851639229258349412352), (-13444454939/2417851639229258349412352)), (147/2417851639229258349412352), by norm_num⟩
  | 15 => ⟨((8237944889/4835703278458516698824704), (9940251771/38685626227668133590597632)), (55/19342813113834066795298816), by norm_num⟩
  | 16 => ⟨((-45680866187/618970019642690137449562112), (-6890057489/618970019642690137449562112)), (155/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-3897271816881/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((27828703702881/9903520314283042199192993792), (-4623459612989/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236536588361829/4951760157141521099596496896), (-5201078363017/39614081257132168796771975168)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((946113032548887/1237940039285380274899124224), (-5525804429699/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773891028098361/154742504910672534362390528), (-5525420133771/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552083628106397/9671406556917033397649408), (-5179672790909/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261001244588043/604462909807314587353088), (-283237800249/37778931862957161709568)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1891384895052967/75557863725914323419136), (-7363415496553/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325057962436973/1180591620717411303424), (-5521889581723/4722366482869645213696)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812573259233575/295147905179352825856), (-3795752450455/295147905179352825856)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914046081168325/36893488147419103232), (-9487739102743/73786976294838206464)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827844111093665/9223372036854775808), (-5335722639013/4611686018427387904)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599083216914401/1152921504606846976), (-10668613620851/1152921504606846976)), (1685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299757595105751/36028797018963968), (-4665922120543/72057594037927936)), (1477/144115188075855872), by norm_num⟩
  | 4 => ⟨((374572676453377/9007199254740992), (-3497840842577/9007199254740992)), (555/9007199254740992), by norm_num⟩
  | 3 => ⟨((1497537383943411/9007199254740992), (-17477959350119/9007199254740992)), (2783/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122198426132911/2251799813685248), (-8730506469251/1125899906842624)), (2795/2251799813685248), by norm_num⟩
  | 1 => ⟨((560125203709173/562949953421312), (-3268609636441/140737488355328)), (2113/562949953421312), by norm_num⟩
  | 0 => ⟨((1114212962081085/1125899906842624), (-26062766098217/562949953421312)), (8579/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114212962081085/1125899906842624), (-26062766098217/562949953421312)), (32726292136764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((550117042480533/562949953421312), (-103168928739879/1125899906842624)), (17775/1125899906842624), by norm_num⟩
  | 2 => ⟨((1065699718563433/1125899906842624), (-201634214939855/1125899906842624)), (18999/562949953421312), by norm_num⟩
  | 3 => ⟨((972608245952039/1125899906842624), (-47713283571707/140737488355328)), (85543/1125899906842624), by norm_num⟩
  | 4 => ⟨((177694997521955/281474976710656), (-659473656743475/1125899906842624)), (51449/281474976710656), by norm_num⟩
  | 5 => ⟨((31220666217027/562949953421312), (-1665301422815821/2251799813685248)), (62615/140737488355328), by norm_num⟩
  | 6 => ⟨((-76539695383011/140737488355328), (-92356024823333/1125899906842624)), (1592929/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-46904149689/2147483648)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1017427393/1073741824), (-74341318385/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1742814674821215/4503599627370496), (105315191590975/4503599627370496)), (4399327/4503599627370496), by norm_num⟩
  | 1 => ⟨((116862647621/274877906944), (-3530900991/137438953472)), (149/137438953472), by norm_num⟩
  | 2 => ⟨((-128386740763/549755813888), (3879091219/274877906944)), (165/274877906944), by norm_num⟩
  | 3 => ⟨((1469242199/17179869184), (-710269547/137438953472)), (61/274877906944), by norm_num⟩
  | 4 => ⟨((-51652081115/2199023255552), (6242486821/4398046511104)), (271/4398046511104), by norm_num⟩
  | 5 => ⟨((90792977677/17592186044416), (-5486458187/17592186044416)), (15/1099511627776), by norm_num⟩
  | 6 => ⟨((-66497520667/70368744177664), (1004581731/17592186044416)), (89/35184372088832), by norm_num⟩
  | 7 => ⟨((83491420995/562949953421312), (-5045238101/562949953421312)), (113/281474976710656), by norm_num⟩
  | 8 => ⟨((-91724701103/4503599627370496), (5542760577/4503599627370496)), (251/4503599627370496), by norm_num⟩
  | 9 => ⟨((44786615025/18014398509481984), (-5412751007/36028797018963968)), (247/36028797018963968), by norm_num⟩
  | 10 => ⟨((-78725001015/288230376151711744), (4757211817/288230376151711744)), (219/288230376151711744), by norm_num⟩
  | 11 => ⟨((125801096059/4611686018427387904), (-3800968263/2305843009213693952)), (353/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-23034438343/9223372036854775808), (2783860295/18446744073709551616)), (261/36893488147419103232), by norm_num⟩
  | 13 => ⟨((124582976129/590295810358705651712), (-7528327705/590295810358705651712)), (89/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-39105253867/2361183241434822606848), (4726121903/4722366482869645213696)), (113/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((91651226559/75557863725914323419136), (-21634065/295147905179352825856)), (67/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-100689163769/1208925819614629174706176), (3042233557/604462909807314587353088)), (297/1208925819614629174706176), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (4013656287443/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780496079187099/633825300114114700748351602688), (2379394404601/316912650057057350374175801344)), (1449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945842070995647/19807040628566084398385987584), (167285847753/1237940039285380274899124224)), (815/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891579466256109/2475880078570760549798248448), (2843582196175/1237940039285380274899124224)), (1733/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773244430919807/154742504910672534362390528), (2843270169843/77371252455336267181195264)), (1733/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775738722568373/4835703278458516698824704), (5330468273835/9671406556917033397649408)), (813/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630235418253809/302231454903657293676544), (2331748088349/302231454903657293676544)), (89/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((945261492994061/37778931862957161709568), (7576936536999/75557863725914323419136)), (1157/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299585421788831/4722366482869645213696), (1420403169293/1180591620717411303424)), (217/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624257686791197/590295810358705651712), (1952611390199/147573952589676412928)), (2389/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456745283454423/18446744073709551616), (9760397281609/73786976294838206464)), (2989/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456648555185139/2305843009213693952), (5488393435673/4611686018427387904)), (3365/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798916674862555/576460752303423488), (685762953271/72057594037927936)), (1685/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197936775783643/144115188075855872), (1199440381899/18014398509481984)), (1477/72057594037927936), by norm_num⟩
  | 4 => ⟨((748325182439935/18014398509481984), (14382952485991/36028797018963968)), (4441/36028797018963968), by norm_num⟩
  | 3 => ⟨((186935886334719/1125899906842624), (17960574617247/9007199254740992)), (87/140737488355328), by norm_num⟩
  | 2 => ⟨((560074183442147/1125899906842624), (17933331213305/2251799813685248)), (5595/2251799813685248), by norm_num⟩
  | 1 => ⟨((69823501543401/70368744177664), (26831646349237/1125899906842624)), (4229/562949953421312), by norm_num⟩
  | 0 => ⟨((1108067746091351/1125899906842624), (26694223542481/562949953421312)), (17181/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108067746091351/1125899906842624), (26694223542481/562949953421312)), (65540318015670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((543993207656001/562949953421312), (105085746733293/1125899906842624)), (4431/140737488355328), by norm_num⟩
  | 2 => ⟨((1041541453738551/1125899906842624), (203094190156499/1125899906842624)), (75127/1125899906842624), by norm_num⟩
  | 3 => ⟨((926868670508165/1125899906842624), (375754570678761/1125899906842624)), (41525/281474976710656), by norm_num⟩
  | 4 => ⟨((318808994751937/562949953421312), (19333153931233/35184372088832)), (48043/140737488355328), by norm_num⟩
  | 5 => ⟨((42304576602565/2251799813685248), (1401436604783351/2251799813685248)), (1715405/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1742814674821215/4503599627370496), (105315191590975/4503599627370496)), (4399327/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-74341318385/2147483648)), (1/1073741824), by norm_num⟩, -6, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-2567700857/2147483648), (-46904149689/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((650862764067717/2251799813685248), (50227569707065/562949953421312)), (1696571/4503599627370496), by norm_num⟩
  | 1 => ⟨((-27535625601/68719476736), (-16999559731/137438953472)), (37/68719476736), by norm_num⟩
  | 2 => ⟨((76344965001/274877906944), (23566393797/274877906944)), (105/274877906944), by norm_num⟩
  | 3 => ⟨((-35278864827/274877906944), (-21779972555/549755813888)), (99/549755813888), by norm_num⟩
  | 4 => ⟨((97813782753/2199023255552), (15096726569/1099511627776)), (35/549755813888), by norm_num⟩
  | 5 => ⟨((-13559869547/1099511627776), (-16742805531/4398046511104)), (79/4398046511104), by norm_num⟩
  | 6 => ⟨((100255843683/35184372088832), (30947275863/35184372088832)), (149/35184372088832), by norm_num⟩
  | 7 => ⟨((-79419491867/140737488355328), (-6128862003/35184372088832)), (15/17592186044416), by norm_num⟩
  | 8 => ⟨((55049396869/562949953421312), (8496406835/281474976710656)), (85/562949953421312), by norm_num⟩
  | 9 => ⟨((-67835260855/4503599627370496), (-20939592685/4503599627370496)), (107/4503599627370496), by norm_num⟩
  | 10 => ⟨((75231711687/36028797018963968), (23222751411/36028797018963968)), (121/36028797018963968), by norm_num⟩
  | 11 => ⟨((-37924835523/144115188075855872), (-2926688121/36028797018963968)), (31/72057594037927936), by norm_num⟩
  | 12 => ⟨((35049990421/1152921504606846976), (10819336637/1152921504606846976)), (117/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-29901294817/9223372036854775808), (-18460043533/18446744073709551616)), (51/9223372036854775808), by norm_num⟩
  | 14 => ⟨((94747420331/295147905179352825856), (29246919149/295147905179352825856)), (41/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-8756520969/295147905179352825856), (-21623914185/2361183241434822606848)), (123/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((97112925139/37778931862957161709568), (7494277575/9444732965739290427392)), (173/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (97501687531/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222515613138505/79228162514264337593543950336), (462222228981/633825300114114700748351602688)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945633663467571/19807040628566084398385987584), (519944645315/39614081257132168796771975168)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891137534035261/2475880078570760549798248448), (276186890549/1237940039285380274899124224)), (431/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772803548974387/154742504910672534362390528), (69037245671/19342813113834066795298816)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387766308477975/2417851639229258349412352), (8089043793/151115727451828646838272)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((315027816731675/151115727451828646838272), (452905928865/604462909807314587353088)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889940775734419/75557863725914323419136), (91977648407/9444732965739290427392)), (1149/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162393824045375/590295810358705651712), (551733846173/4722366482869645213696)), (431/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202957845729043/73786976294838206464), (94802441399/73786976294838206464)), (1185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826241934371771/73786976294838206464), (236925691533/18446744073709551616)), (2963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456442184615029/2305843009213693952), (1065723529785/9223372036854775808)), (3333/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597015507717003/1152921504606846976), (1065171202553/1152921504606846976)), (1667/576460752303423488), by norm_num⟩
  | 5 => ⟨((299307437736071/36028797018963968), (465701906291/72057594037927936)), (1459/72057594037927936), by norm_num⟩
  | 4 => ⟨((93475436279553/2251799813685248), (1395864685163/36028797018963968)), (4377/36028797018963968), by norm_num⟩
  | 3 => ⟨((747106415207397/4503599627370496), (1742661173363/9007199254740992)), (5473/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237837934837917/4503599627370496), (3478821792609/4503599627370496)), (5475/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115443746130911/1125899906842624), (2601005499355/1125899906842624)), (4109/562949953421312), by norm_num⟩
  | 0 => ⟨((1105048480483361/1125899906842624), (5169656551935/1125899906842624)), (8231/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1105048480483361/1125899906842624), (5169656551935/1125899906842624)), (31398775340843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2169118962437935/2251799813685248), (10147831228367/1125899906842624)), (16233/562949953421312), by norm_num⟩
  | 2 => ⟨((2089291033199665/2251799813685248), (4887613235265/281474976710656)), (126267/2251799813685248), by norm_num⟩
  | 3 => ⟨((484457822810005/562949953421312), (72558112451213/2251799813685248)), (238695/2251799813685248), by norm_num⟩
  | 4 => ⟨((1665301422815837/2251799813685248), (62441332434059/1125899906842624)), (426211/2251799813685248), by norm_num⟩
  | 5 => ⟨((1224635126128199/2251799813685248), (184712049646683/2251799813685248)), (338839/1125899906842624), by norm_num⟩
  | 6 => ⟨((650862764067717/2251799813685248), (50227569707065/562949953421312)), (1696571/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-46904149689/1073741824)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-54454031465/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1012536227753849/4503599627370496), (-15237374973431/140737488355328)), (1578061/4503599627370496), by norm_num⟩
  | 1 => ⟨((-24865939219/68719476736), (23948836883/137438953472)), (79/137438953472), by norm_num⟩
  | 2 => ⟨((80040370615/274877906944), (-19272083019/137438953472)), (129/274877906944), by norm_num⟩
  | 3 => ⟨((-42940002331/274877906944), (20678147375/274877906944)), (35/137438953472), by norm_num⟩
  | 4 => ⟨((269958077/4294967296), (-4160024293/137438953472)), (115/1099511627776), by norm_num⟩
  | 5 => ⟨((-88981660445/4398046511104), (42849925209/4398046511104)), (151/4398046511104), by norm_num⟩
  | 6 => ⟨((47736819277/8796093022208), (-22988098059/8796093022208)), (83/8796093022208), by norm_num⟩
  | 7 => ⟨((-2743908813/2199023255552), (42283333201/70368744177664)), (155/70368744177664), by norm_num⟩
  | 8 => ⟨((70658413951/281474976710656), (-34026199759/281474976710656)), (63/140737488355328), by norm_num⟩
  | 9 => ⟨((-25271184499/562949953421312), (24339135959/1125899906842624)), (23/281474976710656), by norm_num⟩
  | 10 => ⟨((8134480485/1125899906842624), (-31337862535/9007199254740992)), (15/1125899906842624), by norm_num⟩
  | 11 => ⟨((-76171294781/72057594037927936), (36680977497/72057594037927936)), (143/72057594037927936), by norm_num⟩
  | 12 => ⟨((10216080805/72057594037927936), (-19678585283/288230376151711744)), (155/576460752303423488), by norm_num⟩
  | 13 => ⟨((-80945958223/4611686018427387904), (4872532495/576460752303423488)), (39/1152921504606846976), by norm_num⟩
  | 14 => ⟨((74444282299/36893488147419103232), (-35849318981/36893488147419103232)), (145/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-63900506825/295147905179352825856), (15385934161/147573952589676412928)), (63/147573952589676412928), by norm_num⟩
  | 16 => ⟨((25710974577/1180591620717411303424), (-24762705757/2361183241434822606848)), (103/2361183241434822606848), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (-584594295227/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444956921619983/158456325028528675187087900672), (-346310383453/316912650057057350374175801344)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945466493036185/19807040628566084398385987584), (-779102413433/39614081257132168796771975168)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945391166598419/1237940039285380274899124224), (-827679064227/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886224194500379/77371252455336267181195264), (-827547187125/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1514387026221/9444732965739290427392), (-775685397239/9671406556917033397649408)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259820006155677/604462909807314587353088), (-678584664213/604462909807314587353088)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472366889589733/18889465931478580854784), (-1102437538563/75557863725914323419136)), (2299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324698937631073/1180591620717411303424), (-206649624845/1180591620717411303424)), (1725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202896871746183/73786976294838206464), (-568099938339/295147905179352825856)), (2371/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825632368000703/73786976294838206464), (-1419690480963/73786976294838206464)), (741/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912541607365499/4611686018427387904), (-798191514973/4611686018427387904)), (3335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596330281937147/1152921504606846976), (-1595422626611/1152921504606846976)), (417/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196630513444199/144115188075855872), (-697457548845/72057594037927936)), (2919/144115188075855872), by norm_num⟩
  | 4 => ⟨((186838599249783/4503599627370496), (-2090215126865/36028797018963968)), (1095/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493091268666073/9007199254740992), (-2608997478791/9007199254740992)), (2739/4503599627370496), by norm_num⟩
  | 2 => ⟨((279449790290485/562949953421312), (-5206697567843/4503599627370496)), (5481/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113768420138411/1125899906842624), (-7781861941153/2251799813685248)), (16463/2251799813685248), by norm_num⟩
  | 0 => ⟨((1101715330065011/1125899906842624), (-15451339943443/2251799813685248)), (16501/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101715330065011/1125899906842624), (-15451339943443/2251799813685248)), (62946323875045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2155994463002287/2251799813685248), (-30238883549559/2251799813685248)), (4065/140737488355328), by norm_num⟩
  | 2 => ⟨((515964796934187/562949953421312), (-14476168153137/562949953421312)), (126293/2251799813685248), by norm_num⟩
  | 3 => ⟨((945057764422113/1125899906842624), (-106143618858119/2251799813685248)), (238001/2251799813685248), by norm_num⟩
  | 4 => ⟨((49422552780201/70368744177664), (-44547410713903/562949953421312)), (421985/2251799813685248), by norm_num⟩
  | 5 => ⟨((274165057750933/562949953421312), (-125149128804717/1125899906842624)), (659537/2251799813685248), by norm_num⟩
  | 6 => ⟨((1012536227753849/4503599627370496), (-15237374973431/140737488355328)), (1578061/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-54454031465/1073741824)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1659352607/1073741824), (-60622734037/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((478231910631537/2251799813685248), (171370640210243/9007199254740992)), (249847/1125899906842624), by norm_num⟩
  | 1 => ⟨((-104599188765/274877906944), (-9370573955/274877906944)), (111/274877906944), by norm_num⟩
  | 2 => ⟨((2928384171/8589934592), (2098726827/68719476736)), (101/274877906944), by norm_num⟩
  | 3 => ⟨((-27983787029/137438953472), (-10027769775/549755813888)), (123/549755813888), by norm_num⟩
  | 4 => ⟨((25070107697/274877906944), (8983675725/1099511627776)), (7/68719476736), by norm_num⟩
  | 5 => ⟨((-71871364577/2199023255552), (-6438634419/2199023255552)), (41/1099511627776), by norm_num⟩
  | 6 => ⟨((42925399349/4398046511104), (7690989459/8796093022208)), (25/2199023255552), by norm_num⟩
  | 7 => ⟨((-21974854501/8796093022208), (-7874516109/35184372088832)), (13/4398046511104), by norm_num⟩
  | 8 => ⟨((39373653637/70368744177664), (3527309701/70368744177664)), (95/140737488355328), by norm_num⟩
  | 9 => ⟨((-3919339819/35184372088832), (-11235716547/1125899906842624)), (153/1125899906842624), by norm_num⟩
  | 10 => ⟨((89888182193/4503599627370496), (8052680607/4503599627370496)), (7/281474976710656), by norm_num⟩
  | 11 => ⟨((-29283273021/9007199254740992), (-10493430349/36028797018963968)), (37/9007199254740992), by norm_num⟩
  | 12 => ⟨((69958108967/144115188075855872), (6267234397/144115188075855872)), (45/72057594037927936), by norm_num⟩
  | 13 => ⟨((-77137294887/1152921504606846976), (-3455192793/576460752303423488)), (101/1152921504606846976), by norm_num⟩
  | 14 => ⟨((19744496935/2305843009213693952), (3537642517/4611686018427387904)), (105/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-75471763943/73786976294838206464), (-3380589055/36893488147419103232)), (51/36893488147419103232), by norm_num⟩
  | 16 => ⟨((16903405963/147573952589676412928), (6057202451/590295810358705651712)), (93/590295810358705651712), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (58192235281/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444896318338905/158456325028528675187087900672), (68927635165/316912650057057350374175801344)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890660321103977/39614081257132168796771975168), (77533008969/19807040628566084398385987584)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890492688205405/2475880078570760549798248448), (164731669567/2475880078570760549798248448)), (1723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772158813216609/154742504910672534362390528), (164702455967/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387615227766145/2417851639229258349412352), (154377520349/9671406556917033397649408)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259582601331659/604462909807314587353088), (2110145413/9444732965739290427392)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1844806555919/73786976294838206464), (219396970707/75557863725914323419136)), (2297/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298506637174651/4722366482869645213696), (164496862327/4722366482869645213696)), (1723/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622777638790345/590295810358705651712), (226100561755/590295810358705651712)), (2369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456283998094673/18446744073709551616), (141250911843/36893488147419103232)), (2961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824525195250253/9223372036854775808), (39705538993/1152921504606846976)), (3331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797886382963475/576460752303423488), (158715826047/576460752303423488)), (3331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598071626397125/72057594037927936), (277513645307/144115188075855872)), (2915/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493979033379133/36028797018963968), (415792847133/36028797018963968)), (1093/9007199254740992), by norm_num⟩
  | 3 => ⟨((746090521476803/4503599627370496), (259453150343/4503599627370496)), (5465/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233783783856775/4503599627370496), (517656316895/2251799813685248)), (10931/4503599627370496), by norm_num⟩
  | 1 => ⟨((278103721532493/281474976710656), (1546734080703/2251799813685248)), (16401/2251799813685248), by norm_num⟩
  | 0 => ⟨((1099037613610767/1125899906842624), (3068618768397/2251799813685248)), (16409/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1099037613610767/1125899906842624), (3068618768397/2251799813685248)), (62595371726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536407061891159/562949953421312), (5990812198853/2251799813685248)), (2005/70368744177664), by norm_num⟩
  | 2 => ⟨((255555836876447/281474976710656), (11416695037981/2251799813685248)), (30653/562949953421312), by norm_num⟩
  | 3 => ⟨((1856129449170647/2251799813685248), (5182704141039/562949953421312)), (13993/140737488355328), by norm_num⟩
  | 4 => ⟨((764896316357147/1125899906842624), (34176287693275/2251799813685248)), (373219/2251799813685248), by norm_num⟩
  | 5 => ⟨((2077535903725225/4503599627370496), (92872612936461/4503599627370496)), (1036865/4503599627370496), by norm_num⟩
  | 6 => ⟨((478231910631537/2251799813685248), (171370640210243/9007199254740992)), (249847/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-60622734037/1073741824)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-65838297747/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((93503153799455/9007199254740992), (1678882137072049/9007199254740992)), (4128871/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1388158691/68719476736), (-99699517505/274877906944)), (247/274877906944), by norm_num⟩
  | 2 => ⟨((5402464171/274877906944), (24250787871/68719476736)), (121/137438953472), by norm_num⟩
  | 3 => ⟨((-876059155/68719476736), (-31459902827/137438953472)), (79/137438953472), by norm_num⟩
  | 4 => ⟨((1704732401/274877906944), (61218144199/549755813888)), (155/549755813888), by norm_num⟩
  | 5 => ⟨((-5307609729/2199023255552), (-47650003241/1099511627776)), (243/2199023255552), by norm_num⟩
  | 6 => ⟨((6885421093/8796093022208), (123630166545/8796093022208)), (317/8796093022208), by norm_num⟩
  | 7 => ⟨((-3828117367/17592186044416), (-34367599401/8796093022208)), (89/8796093022208), by norm_num⟩
  | 8 => ⟨((1862293109/35184372088832), (66876260473/70368744177664)), (87/35184372088832), by norm_num⟩
  | 9 => ⟨((-3221204499/281474976710656), (-115675727987/562949953421312)), (303/562949953421312), by norm_num⟩
  | 10 => ⟨((5014539621/2251799813685248), (90037829235/2251799813685248)), (119/1125899906842624), by norm_num⟩
  | 11 => ⟨((-7096613485/18014398509481984), (-63711100257/9007199254740992)), (339/18014398509481984), by norm_num⟩
  | 12 => ⟨((1150781017/18014398509481984), (82650717731/72057594037927936)), (111/36028797018963968), by norm_num⟩
  | 13 => ⟨((-5512163595/576460752303423488), (-98972843359/576460752303423488)), (67/144115188075855872), by norm_num⟩
  | 14 => ⟨((766155363/576460752303423488), (110052720213/4611686018427387904)), (75/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-3180521593/18446744073709551616), (-114214776103/36893488147419103232)), (313/36893488147419103232), by norm_num⟩
  | 16 => ⟨((6189009247/295147905179352825856), (111125845995/295147905179352825856)), (153/147573952589676412928), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (123354075391/633825300114114700748351602688)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779377246849555/633825300114114700748351602688), (1168628856769/316912650057057350374175801344)), (1445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890426156500815/39614081257132168796771975168), (1314511077575/19807040628566084398385987584)), (813/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945121857190763/1237940039285380274899124224), (2792857307073/2475880078570760549798248448)), (27/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1771909643855381/154742504910672534362390528), (2792318829203/154742504910672534362390528)), (27/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1550227107149893/9671406556917033397649408), (2617226876995/9671406556917033397649408)), (405/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259377815402667/604462909807314587353088), (2289501612719/604462909807314587353088)), (709/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888748747343639/75557863725914323419136), (464921006997/9444732965739290427392)), (2305/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298256422838009/4722366482869645213696), (2788588241881/4722366482869645213696)), (865/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622433042278913/590295810358705651712), (3832785388311/590295810358705651712)), (1189/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456176104995019/18446744073709551616), (2394348705213/36893488147419103232)), (1487/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912019270515811/4611686018427387904), (2692072503527/4611686018427387904)), (3347/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99705293431523/72057594037927936), (672527822853/144115188075855872)), (1675/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195714599881923/144115188075855872), (4703284851379/144115188075855872)), (2933/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493332880307737/36028797018963968), (3523057252393/18014398509481984)), (4405/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491367815229403/9007199254740992), (8792236625667/9007199254740992)), (5515/9007199254740992), by norm_num⟩
  | 2 => ⟨((558035197374313/1125899906842624), (17538317095749/4503599627370496)), (5527/2251799813685248), by norm_num⟩
  | 1 => ⟨((138895261167587/140737488355328), (26192306905989/2251799813685248)), (16645/2251799813685248), by norm_num⟩
  | 0 => ⟨((2192901098429757/2251799813685248), (51925267885765/2251799813685248)), (2097/140737488355328), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2192901098429757/2251799813685248), (51925267885765/2251799813685248)), (7999420702886537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((533586396628197/562949953421312), (50567095836375/1125899906842624)), (66897/2251799813685248), by norm_num⟩
  | 2 => ⟨((2018475590200327/2251799813685248), (191718033131025/2251799813685248)), (132825/2251799813685248), by norm_num⟩
  | 3 => ⟨((1793004813069623/2251799813685248), (171852829778359/1125899906842624)), (130371/1125899906842624), by norm_num⟩
  | 4 => ⟨((1375225568658107/2251799813685248), (547354074833053/2251799813685248)), (30927/140737488355328), by norm_num⟩
  | 5 => ⟨((706834094123939/2251799813685248), (334281632960839/1125899906842624)), (844973/2251799813685248), by norm_num⟩
  | 6 => ⟨((93503153799455/9007199254740992), (1678882137072049/9007199254740992)), (4128871/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-65838297747/1073741824)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1925775643/1073741824), (-35178112267/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-168744763442951/1125899906842624), (-325307762419965/4503599627370496)), (4163401/4503599627370496), by norm_num⟩
  | 1 => ⟨((42833846563/137438953472), (41287748719/274877906944)), (531/274877906944), by norm_num⟩
  | 2 => ⟨((-89070479933/274877906944), (-42927729925/274877906944)), (555/274877906944), by norm_num⟩
  | 3 => ⟨((61738952037/274877906944), (29755234965/274877906944)), (387/274877906944), by norm_num⟩
  | 4 => ⟨((-64191270803/549755813888), (-15468567917/274877906944)), (405/549755813888), by norm_num⟩
  | 5 => ⟨((53392798049/1099511627776), (12866393087/549755813888)), (339/1099511627776), by norm_num⟩
  | 6 => ⟨((-18504533715/1099511627776), (-35673216369/4398046511104)), (59/549755813888), by norm_num⟩
  | 7 => ⟨((87952219695/17592186044416), (42388781739/17592186044416)), (563/17592186044416), by norm_num⟩
  | 8 => ⟨((-91445749659/70368744177664), (-44072496825/70368744177664)), (147/17592186044416), by norm_num⟩
  | 9 => ⟨((84513818067/281474976710656), (20365817943/140737488355328)), (273/140737488355328), by norm_num⟩
  | 10 => ⟨((-35148308827/562949953421312), (-33879622289/1125899906842624)), (57/140737488355328), by norm_num⟩
  | 11 => ⟨((53155529815/4503599627370496), (25618434183/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 12 => ⟨((-73689211245/36028797018963968), (-35514690849/36028797018963968)), (121/9007199254740992), by norm_num⟩
  | 13 => ⟨((47148432935/144115188075855872), (1420206221/9007199254740992)), (39/18014398509481984), by norm_num⟩
  | 14 => ⟨((-28012117163/576460752303423488), (-13500506577/576460752303423488)), (373/1152921504606846976), by norm_num⟩
  | 15 => ⟨((31066432053/4611686018427387904), (935783807/288230376151711744)), (13/288230376151711744), by norm_num⟩
  | 16 => ⟨((-64600829363/73786976294838206464), (-31134523557/73786976294838206464)), (435/73786976294838206464), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-876816266841/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889596650873159/316912650057057350374175801344), (-2076295719503/316912650057057350374175801344)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890218889002791/39614081257132168796771975168), (-4670905534225/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890023066756837/2475880078570760549798248448), (-2480963194743/1237940039285380274899124224)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885844258699379/77371252455336267181195264), (-4960901780003/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387504823160215/2417851639229258349412352), (-4649756848221/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629597734795967/302231454903657293676544), (-2033724379039/302231454903657293676544)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888451483408561/75557863725914323419136), (-3303781754059/37778931862957161709568)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649016321308249/2361183241434822606848), (-2476943591061/2361183241434822606848)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811061996695513/295147905179352825856), (-6808693867225/590295810358705651712)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824316084616803/73786976294838206464), (-1063314553681/9223372036854775808)), (5969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455899721062825/2305843009213693952), (-9563849479743/9223372036854775808)), (6721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199355196190939/144115188075855872), (-9556374091189/1152921504606846976)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597661485470047/72057594037927936), (-32630545217/562949953421312)), (737/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492737668239087/36028797018963968), (-12513319024129/36028797018963968)), (8863/36028797018963968), by norm_num⟩
  | 3 => ⟨((186326281192573/1125899906842624), (-7806121192421/4503599627370496)), (11109/9007199254740992), by norm_num⟩
  | 2 => ⟨((139411574016149/281474976710656), (-15568156356499/2251799813685248)), (11155/2251799813685248), by norm_num⟩
  | 1 => ⟨((138743137996493/140737488355328), (-23242102694087/1125899906842624)), (1053/70368744177664), by norm_num⟩
  | 0 => ⟨((546908656929525/562949953421312), (-23022091707305/562949953421312)), (17081/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546908656929525/562949953421312), (-23022091707305/562949953421312)), (65158846141624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((530382959450075/562949953421312), (-89464302670809/1125899906842624)), (17293/281474976710656), by norm_num⟩
  | 2 => ⟨((992291114385773/1125899906842624), (-84288738860893/562949953421312)), (70667/562949953421312), by norm_num⟩
  | 3 => ⟨((849296890320801/1125899906842624), (-74286325192971/281474976710656)), (36431/140737488355328), by norm_num⟩
  | 4 => ⟨((562225713218973/1125899906842624), (-448289547561487/1125899906842624)), (1187063/2251799813685248), by norm_num⟩
  | 5 => ⟨((409038968568965/4503599627370496), (-447712819007449/1125899906842624)), (2130821/2251799813685248), by norm_num⟩
  | 6 => ⟨((-168744763442951/1125899906842624), (-325307762419965/4503599627370496)), (4163401/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-35178112267/536870912)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨63,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile063Terms0

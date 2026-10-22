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
namespace Reinmann.XiBand97.Tile021Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28251/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28251/1280))
  have he : value ((69/80), (28251/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1026666057/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1136114993749135/2251799813685248), (-246522032184959/1125899906842624)), (13434791/562949953421312), by norm_num⟩
  | 1 => ⟨((751013665/2147483648), (325920203/2147483648)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((-1041126009/8589934592), (-112955335/2147483648)), (53/8589934592), by norm_num⟩
  | 3 => ⟨((120275593/4294967296), (1631139/134217728)), (51/34359738368), by norm_num⟩
  | 4 => ⟨((-1333899011/274877906944), (-144719283/68719476736)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((739670671/1099511627776), (641995283/2199023255552)), (83/2199023255552), by norm_num⟩
  | 6 => ⟨((-1367201707/17592186044416), (-593329627/17592186044416)), (79/17592186044416), by norm_num⟩
  | 7 => ⟨((270763431/35184372088832), (235008433/70368744177664)), (65/140737488355328), by norm_num⟩
  | 8 => ⟨((-750715635/1125899906842624), (-162895433/562949953421312)), (47/1125899906842624), by norm_num⟩
  | 9 => ⟨((462539045/9007199254740992), (50182449/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | 10 => ⟨((-64121527/18014398509481984), (-445232935/288230376151711744)), (17/72057594037927936), by norm_num⟩
  | 11 => ⟨((1034371623/4611686018427387904), (224445057/2305843009213693952)), (71/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-477981183/36893488147419103232), (-103715639/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 13 => ⟨((815535531/1180591620717411303424), (176960499/590295810358705651712)), (15/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-646041319/18889465931478580854784), (-140182481/9444732965739290427392)), (97/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((955310333/604462909807314587353088), (207289795/302231454903657293676544)), (37/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-82771333/1208925819614629174706176), (-143682337/4835703278458516698824704)), (105/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-3558924941371/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781038928300125/633825300114114700748351602688), (-4222067770785/633825300114114700748351602688)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892294949519621/39614081257132168796771975168), (-593693102651/4951760157141521099596496896)), (26055/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473057146954571/618970019642690137449562112), (-5046080293631/2475880078570760549798248448)), (6923/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773893708240097/154742504910672534362390528), (-2522865053825/77371252455336267181195264)), (6925/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552086307967927/9671406556917033397649408), (-4729999703275/9671406556917033397649408)), (12989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261003756660247/604462909807314587353088), (-2069188621425/302231454903657293676544)), (5685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891389290582785/75557863725914323419136), (-6724164109137/75557863725914323419136)), (18485/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300235420556011/4722366482869645213696), (-5042511057739/4722366482869645213696)), (27743/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625151873698381/590295810358705651712), (-3466228635249/295147905179352825856)), (19085/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914049762091671/36893488147419103232), (-4332038436241/36893488147419103232)), (47749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827853311003819/9223372036854775808), (-9745028706507/9223372036854775808)), (6721/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599093563509607/1152921504606846976), (-9742452679267/1152921504606846976)), (6729/144115188075855872), by norm_num⟩
  | 5 => ⟨((599520361439683/72057594037927936), (-8521742832137/144115188075855872)), (23587/72057594037927936), by norm_num⟩
  | 4 => ⟨((374577198943655/9007199254740992), (-12776794659945/36028797018963968)), (8863/4503599627370496), by norm_num⟩
  | 3 => ⟨((374391125036897/2251799813685248), (-3990194923377/2251799813685248)), (5555/562949953421312), by norm_num⟩
  | 2 => ⟨((280558072114435/562949953421312), (-15945400646589/2251799813685248)), (11157/281474976710656), by norm_num⟩
  | 1 => ⟨((1120318032720347/1125899906842624), (-23879448722563/1125899906842624)), (16853/140737488355328), by norm_num⟩
  | 0 => ⟨((557207668685857/562949953421312), (-47603064434853/1125899906842624)), (273421/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557207668685857/562949953421312), (-47603064434853/1125899906842624)), (1043018345359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101035256235259/1125899906842624), (-47117496670607/562949953421312)), (564385/1125899906842624), by norm_num⟩
  | 2 => ⟨((267208122629153/281474976710656), (-184307769117303/1125899906842624)), (599159/562949953421312), by norm_num⟩
  | 3 => ⟨((492243374517785/562949953421312), (-87482968374889/281474976710656)), (1333743/562949953421312), by norm_num⟩
  | 4 => ⟨((376037797760505/562949953421312), (-611960779873585/1125899906842624)), (6323019/1125899906842624), by norm_num⟩
  | 5 => ⟨((169750174161361/1125899906842624), (-1635103671869331/2251799813685248)), (30641545/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1136114993749135/2251799813685248), (-246522032184959/1125899906842624)), (13434791/562949953421312), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1026666057/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1627227201/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((552747328979695/2251799813685248), (675717368293411/2251799813685248)), (51643753/2251799813685248), by norm_num⟩
  | 1 => ⟨((-579123505/2147483648), (-176990367/536870912)), (7/268435456), by norm_num⟩
  | 2 => ⟨((636232199/4294967296), (777775169/4294967296)), (1/67108864), by norm_num⟩
  | 3 => ⟨((-465981675/8589934592), (-284824453/4294967296)), (3/536870912), by norm_num⟩
  | 4 => ⟨((511933195/34359738368), (625823289/34359738368)), (55/34359738368), by norm_num⟩
  | 5 => ⟨((-899865759/274877906944), (-550029725/137438953472)), (25/68719476736), by norm_num⟩
  | 6 => ⟨((329534527/549755813888), (402846277/549755813888)), (19/274877906944), by norm_num⟩
  | 7 => ⟨((-827498699/8796093022208), (-1011592847/8796093022208)), (49/4398046511104), by norm_num⟩
  | 8 => ⟨((56818765/4398046511104), (1111348333/70368744177664)), (55/35184372088832), by norm_num⟩
  | 9 => ⟨((-443888309/281474976710656), (-16957513/8796093022208)), (55/281474976710656), by norm_num⟩
  | 10 => ⟨((390128921/2251799813685248), (953842287/4503599627370496)), (99/4503599627370496), by norm_num⟩
  | 11 => ⟨((-623418803/36028797018963968), (-381055585/18014398509481984)), (81/36028797018963968), by norm_num⟩
  | 12 => ⟨((456597039/288230376151711744), (1116352929/576460752303423488)), (61/288230376151711744), by norm_num⟩
  | 13 => ⟨((-617382299/4611686018427387904), (-754731721/4611686018427387904)), (21/1152921504606846976), by norm_num⟩
  | 14 => ⟨((387579303/36893488147419103232), (947608621/73786976294838206464)), (27/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-454186011/590295810358705651712), (-277614527/295147905179352825856)), (129/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((498974333/9444732965739290427392), (304990731/4722366482869645213696)), (73/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (1153028075247/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780507159664949/633825300114114700748351602688), (341771735559/158456325028528675187087900672)), (5771/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945848634649433/19807040628566084398385987584), (384460385441/9903520314283042199192993792)), (51943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945797116251431/1237940039285380274899124224), (1633798525021/2475880078570760549798248448)), (27597/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773260117767877/154742504910672534362390528), (1633620664623/154742504910672534362390528)), (1725/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1551493129408793/9671406556917033397649408), (95708150993/604462909807314587353088)), (12939/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260485537775181/604462909807314587353088), (669862589307/302231454903657293676544)), (11323/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890548707730367/75557863725914323419136), (2176699208135/75557863725914323419136)), (73611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299606315569565/4722366482869645213696), (1632214521429/4722366482869645213696)), (27609/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624289018474127/590295810358705651712), (2243791491651/590295810358705651712)), (75941/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28547253129247/1152921504606846976), (2803984304323/73786976294838206464)), (47475/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826648031886093/9223372036854775808), (3153444382705/9223372036854775808)), (106851/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597893857109171/1152921504606846976), (788036826341/288230376151711744)), (26723/288230376151711744), by norm_num⟩
  | 5 => ⟨((598998622728363/72057594037927936), (1378335095981/72057594037927936)), (93577/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496756101909617/36028797018963968), (4132089166793/36028797018963968)), (140457/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495645526305241/9007199254740992), (5160011124587/9007199254740992)), (175733/9007199254740992), by norm_num⟩
  | 2 => ⟨((2240692227585463/4503599627370496), (10304732758129/4503599627370496)), (351951/4503599627370496), by norm_num⟩
  | 1 => ⟨((69848164034685/70368744177664), (15418915688957/2251799813685248)), (529141/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218494136783339/2251799813685248), (7671334799335/562949953421312)), (66447/140737488355328), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218494136783339/2251799813685248), (7671334799335/562949953421312)), (253475189745855287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((273157865488005/281474976710656), (30231481804369/1125899906842624)), (2123831/2251799813685248), by norm_num⟩
  | 2 => ⟨((264883574886481/281474976710656), (58676384925753/1125899906842624)), (4236205/2251799813685248), by norm_num⟩
  | 3 => ⟨((1988045308405469/2251799813685248), (220870938968413/2251799813685248)), (8414549/2251799813685248), by norm_num⟩
  | 4 => ⟨((216690009080101/281474976710656), (195000208859881/1125899906842624)), (4127151/562949953421312), by norm_num⟩
  | 5 => ⟨((158372843529875/281474976710656), (300236969710491/1125899906842624)), (15568151/1125899906842624), by norm_num⟩
  | 6 => ⟨((552747328979695/2251799813685248), (675717368293411/2251799813685248)), (51643753/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1627227201/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1026666057/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((930513292739389/4503599627370496), (248758682146325/1125899906842624)), (38962963/2251799813685248), by norm_num⟩
  | 1 => ⟨((-307551701/1073741824), (-657754437/2147483648)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((426357189/2147483648), (911841267/4294967296)), (77/4294967296), by norm_num⟩
  | 3 => ⟨((-788075423/8589934592), (-842720271/8589934592)), (73/8589934592), by norm_num⟩
  | 4 => ⟨((273126129/8589934592), (146032295/4294967296)), (13/4294967296), by norm_num⟩
  | 5 => ⟨((-151453285/17179869184), (-647819991/68719476736)), (59/68719476736), by norm_num⟩
  | 6 => ⟨((559890227/274877906944), (18709775/8589934592)), (57/274877906944), by norm_num⟩
  | 7 => ⟨((-443527237/1099511627776), (-474281245/1099511627776)), (23/549755813888), by norm_num⟩
  | 8 => ⟨((153714827/2199023255552), (82186677/1099511627776)), (33/4398046511104), by norm_num⟩
  | 9 => ⟨((-189416887/17592186044416), (-810203925/70368744177664)), (83/70368744177664), by norm_num⟩
  | 10 => ⟨((105035025/70368744177664), (449272453/281474976710656)), (47/281474976710656), by norm_num⟩
  | 11 => ⟨((-423591165/2251799813685248), (-905925627/4503599627370496)), (97/4503599627370496), by norm_num⟩
  | 12 => ⟨((782962725/36028797018963968), (837253059/36028797018963968)), (23/9007199254740992), by norm_num⟩
  | 13 => ⟨((-667948807/288230376151711744), (-89283015/36028797018963968)), (81/288230376151711744), by norm_num⟩
  | 14 => ⟨((4133811/18014398509481984), (565817327/2305843009213693952)), (33/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-391214345/18446744073709551616), (-836681995/36893488147419103232)), (25/9223372036854775808), by norm_num⟩
  | 16 => ⟨((8474035/4611686018427387904), (289971883/147573952589676412928)), (71/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1066700501145/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890062083047169/316912650057057350374175801344), (158026971051/79228162514264337593543950336)), (46163/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29551038311647/618970019642690137449562112), (1422090728065/39614081257132168796771975168)), (51937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891136549828451/2475880078570760549798248448), (377696742619/618970019642690137449562112)), (13797/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110800156465405/9671406556917033397649408), (1510579521011/154742504910672534362390528)), (55193/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551064188599701/9671406556917033397649408), (1415947919955/9671406556917033397649408)), (51749/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260110287175605/604462909807314587353088), (309683521821/151115727451828646838272)), (22643/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944969530813993/37778931862957161709568), (2012529830731/75557863725914323419136)), (73599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649574600040341/2361183241434822606848), (754518012989/2361183241434822606848)), (55209/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202957584769941/73786976294838206464), (2074337499321/590295810358705651712)), (75927/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826239065040825/73786976294838206464), (2592041586527/73786976294838206464)), (47465/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912882576812073/4611686018427387904), (1457418411539/4611686018427387904)), (53413/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597011477288019/1152921504606846976), (2913325021255/1152921504606846976)), (106865/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197225723652347/144115188075855872), (318432438813/18014398509481984)), (93549/144115188075855872), by norm_num⟩
  | 4 => ⟨((747799969882123/18014398509481984), (3817791733501/36028797018963968)), (140409/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494202283441857/9007199254740992), (4766299009145/9007199254740992)), (175661/9007199254740992), by norm_num⟩
  | 2 => ⟨((559452904164165/1125899906842624), (9514796126787/4503599627370496)), (351771/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230835003403383/2251799813685248), (3556939922023/562949953421312)), (33049/140737488355328), by norm_num⟩
  | 0 => ⟨((2209940230198437/2251799813685248), (28278202253947/2251799813685248)), (1062085/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209940230198437/2251799813685248), (28278202253947/2251799813685248)), (4051532753951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((542125917971293/562949953421312), (6938131935495/281474976710656)), (16495/17592186044416), by norm_num⟩
  | 2 => ⟨((1043460287907293/1125899906842624), (53451872539315/1125899906842624)), (2085303/1125899906842624), by norm_num⟩
  | 3 => ⟨((1929038741653265/2251799813685248), (198152272578005/2251799813685248)), (4063229/1125899906842624), by norm_num⟩
  | 4 => ⟨((1635103671869313/2251799813685248), (169750174161369/1125899906842624)), (7676761/1125899906842624), by norm_num⟩
  | 5 => ⟨((71007187109319/140737488355328), (30815254023121/140737488355328)), (13463509/1125899906842624), by norm_num⟩
  | 6 => ⟨((930513292739389/4503599627370496), (248758682146325/1125899906842624)), (38962963/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1026666057/33554432)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1191922381/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-640352831153877/4503599627370496), (923540858776233/4503599627370496)), (25070897/1125899906842624), by norm_num⟩
  | 1 => ⟨((491432249/2147483648), (-708762013/2147483648)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-790929693/4294967296), (1140708455/4294967296)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((848634823/8589934592), (-1223932957/8589934592)), (141/8589934592), by norm_num⟩
  | 4 => ⟨((-682912529/17179869184), (246230513/4294967296)), (115/17179869184), by norm_num⟩
  | 5 => ⟨((219821063/17179869184), (-1268136713/68719476736)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((-117929451/34359738368), (680329101/137438953472)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((867657735/1099511627776), (-19552633/17179869184)), (153/1099511627776), by norm_num⟩
  | 8 => ⟨((-698220627/4398046511104), (1006999963/4398046511104)), (125/4398046511104), by norm_num⟩
  | 9 => ⟨((249720611/8796093022208), (-720312853/17592186044416)), (91/17592186044416), by norm_num⟩
  | 10 => ⟨((-321527855/70368744177664), (231859763/35184372088832)), (119/140737488355328), by norm_num⟩
  | 11 => ⟨((376348451/562949953421312), (-1085567689/1125899906842624)), (71/562949953421312), by norm_num⟩
  | 12 => ⟨((-807612621/9007199254740992), (1164769197/9007199254740992)), (77/4503599627370496), by norm_num⟩
  | 13 => ⟨((399939191/36028797018963968), (-288403647/18014398509481984)), (155/72057594037927936), by norm_num⟩
  | 14 => ⟨((-183907799/144115188075855872), (132619361/72057594037927936)), (145/576460752303423488), by norm_num⟩
  | 15 => ⟨((157860365/1152921504606846976), (-28459017/144115188075855872)), (127/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-508132913/36893488147419103232), (732848335/36893488147419103232)), (13/4611686018427387904), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (2835859530039/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779821913557817/633825300114114700748351602688), (1679947288715/316912650057057350374175801344)), (23133/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890926154204945/39614081257132168796771975168), (1889701838589/19807040628566084398385987584)), (52059/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472693662194269/618970019642690137449562112), (501880770111/309485009821345068724781056)), (27663/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772440226042843/154742504910672534362390528), (1003601154303/38685626227668133590597632)), (55339/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775362076923729/4835703278458516698824704), (1881411357839/4835703278458516698824704)), (51895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314953089323101/151115727451828646838272), (3291788293791/604462909807314587353088)), (45423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472363544250295/18889465931478580854784), (668484759423/9444732965739290427392)), (4615/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298784882063679/4722366482869645213696), (4009790457447/4722366482869645213696)), (13851/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623158678088829/590295810358705651712), (1377911272631/147573952589676412928)), (76219/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825609972228395/73786976294838206464), (6886831395607/73786976294838206464)), (95333/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825055236605487/9223372036854775808), (3871969420285/4611686018427387904)), (53665/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199537353668523/144115188075855872), (7739256269765/1152921504606846976)), (107431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299149772336209/36028797018963968), (6766582074253/144115188075855872)), (23529/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494653865889833/36028797018963968), (10139340624497/36028797018963968)), (70701/18014398509481984), by norm_num⟩
  | 3 => ⟨((746504502272119/4503599627370496), (12655748090787/9007199254740992)), (177151/9007199254740992), by norm_num⟩
  | 2 => ⟨((279424138719697/562949953421312), (12628114954389/2251799813685248)), (177751/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113563878371491/1125899906842624), (18873119316799/1125899906842624)), (134063/562949953421312), by norm_num⟩
  | 0 => ⟨((550552526554009/562949953421312), (37470207179875/1125899906842624)), (542269/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550552526554009/562949953421312), (37470207179875/1125899906842624)), (2068592075828170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1075609220849845/1125899906842624), (9161257189919/140737488355328)), (1096749/1125899906842624), by norm_num⟩
  | 2 => ⟨((127849260450177/140737488355328), (70016403043765/562949953421312)), (2238307/1125899906842624), by norm_num⟩
  | 3 => ⟨((911713860557939/1125899906842624), (254418220848915/1125899906842624)), (2311719/562949953421312), by norm_num⟩
  | 4 => ⟨((1361566028694365/2251799813685248), (412037725408337/1125899906842624)), (19154597/2251799813685248), by norm_num⟩
  | 5 => ⟨((521698995939275/2251799813685248), (996565620170899/2251799813685248)), (37183663/2251799813685248), by norm_num⟩
  | 6 => ⟨((-640352831153877/4503599627370496), (923540858776233/4503599627370496)), (25070897/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1191922381/33554432)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1326946629/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-16366135701099/281474976710656), (-923902219888883/4503599627370496)), (41010865/2251799813685248), by norm_num⟩
  | 1 => ⟨((6991429/67108864), (789361263/2147483648)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((-100215673/1073741824), (-707172759/2147483648)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((59854127/1073741824), (844722325/4294967296)), (39/2147483648), by norm_num⟩
  | 4 => ⟨((-428976795/17179869184), (-1513539225/17179869184)), (71/8589934592), by norm_num⟩
  | 5 => ⟨((153724647/17179869184), (4237341/134217728)), (13/4294967296), by norm_num⟩
  | 6 => ⟨((-367250123/137438953472), (-1295751827/137438953472)), (63/68719476736), by norm_num⟩
  | 7 => ⟨((376013649/549755813888), (1326671775/549755813888)), (131/549755813888), by norm_num⟩
  | 8 => ⟨((-10526969/68719476736), (-594269179/1099511627776)), (119/2199023255552), by norm_num⟩
  | 9 => ⟨((67064165/2199023255552), (946477715/8796093022208)), (97/8796093022208), by norm_num⟩
  | 10 => ⟨((-384521129/70368744177664), (-1356688327/70368744177664)), (141/70368744177664), by norm_num⟩
  | 11 => ⟨((125267159/140737488355328), (55246799/17592186044416)), (47/140737488355328), by norm_num⟩
  | 12 => ⟨((-37408103/281474976710656), (-1055882403/2251799813685248)), (57/1125899906842624), by norm_num⟩
  | 13 => ⟨((329975743/18014398509481984), (1164238335/18014398509481984)), (127/18014398509481984), by norm_num⟩
  | 14 => ⟨((-337849807/144115188075855872), (-1192020035/144115188075855872)), (131/144115188075855872), by norm_num⟩
  | 15 => ⟨((161425491/576460752303423488), (569550183/576460752303423488)), (127/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-72308913/2305843009213693952), (-510248467/4611686018427387904)), (115/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-601474216531/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779580944015013/633825300114114700748351602688), (-2849740702201/633825300114114700748351602688)), (1445/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((945327599806627/19807040628566084398385987584), (-3205513037747/39614081257132168796771975168)), (26015/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945243463854235/1237940039285380274899124224), (-3405319729595/2475880078570760549798248448)), (13823/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443038173534477/38685626227668133590597632), (-3404714676361/154742504910672534362390528)), (6913/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550454793615929/9671406556917033397649408), (-1595638610165/4835703278458516698824704)), (12965/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259576867955045/604462909807314587353088), (-1395862434651/302231454903657293676544)), (22695/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472267970828503/18889465931478580854784), (-141729626401/2361183241434822606848)), (36891/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298498491087313/4722366482869645213696), (-1700228483123/2361183241434822606848)), (13839/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811382712667711/295147905179352825856), (-2336957914543/295147905179352825856)), (19037/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456279802024505/18446744073709551616), (-5839826667313/73786976294838206464)), (95235/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912252114361287/4611686018427387904), (-6566274861561/9223372036854775808)), (13401/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595749197579449/1152921504606846976), (-1640465931283/288230376151711744)), (53647/576460752303423488), by norm_num⟩
  | 5 => ⟨((149514963521987/18014398509481984), (-2868335173165/72057594037927936)), (93979/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493937883643623/36028797018963968), (-8595089985119/36028797018963968)), (141161/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492119424933821/9007199254740992), (-10726522213107/9007199254740992)), (88395/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116815055678245/2251799813685248), (-10700535669271/2251799813685248)), (88649/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112261771468887/1125899906842624), (-15985920760833/1125899906842624)), (66805/281474976710656), by norm_num⟩
  | 0 => ⟨((17165328936583/17592186044416), (-15856406567243/562949953421312)), (539547/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((17165328936583/17592186044416), (-15856406567243/562949953421312)), (2058208469871139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1071031818937819/1125899906842624), (-7735833221401/140737488355328)), (541653/562949953421312), by norm_num⟩
  | 2 => ⟨((1015435911157581/1125899906842624), (-58870764449045/562949953421312)), (2180119/1125899906842624), by norm_num⟩
  | 3 => ⟨((451748426240591/562949953421312), (-424758811866321/2251799813685248)), (2194211/562949953421312), by norm_num⟩
  | 4 => ⟨((1369929148571601/2251799813685248), (-340854677447371/1125899906842624)), (4349353/562949953421312), by norm_num⟩
  | 5 => ⟨((627044295400439/2251799813685248), (-829464067319429/2251799813685248)), (31701931/2251799813685248), by norm_num⟩
  | 6 => ⟨((-16366135701099/281474976710656), (-923902219888883/4503599627370496)), (41010865/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1326946629/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-360277001/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((429992534315215/4503599627370496), (722463456390897/4503599627370496)), (54383073/4503599627370496), by norm_num⟩
  | 1 => ⟨((-398982447/2147483648), (-670361029/2147483648)), (103/4294967296), by norm_num⟩
  | 2 => ⟨((776383993/4294967296), (652231165/2147483648)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-125897791/1073741824), (-423061081/2147483648)), (17/1073741824), by norm_num⟩
  | 4 => ⟨((489971579/8589934592), (823238851/8589934592)), (17/2147483648), by norm_num⟩
  | 5 => ⟨((-762752535/34359738368), (-320389767/8589934592)), (27/8589934592), by norm_num⟩
  | 6 => ⟨((123687325/17179869184), (415633133/34359738368)), (9/8589934592), by norm_num⟩
  | 7 => ⟨((-137533955/68719476736), (-28885169/8589934592)), (41/137438953472), by norm_num⟩
  | 8 => ⟨((267628719/549755813888), (112415887/137438953472)), (81/1099511627776), by norm_num⟩
  | 9 => ⟨((-115729209/1099511627776), (-777782099/4398046511104)), (9/549755813888), by norm_num⟩
  | 10 => ⟨((90079457/4398046511104), (4729669/137438953472)), (57/17592186044416), by norm_num⟩
  | 11 => ⟨((-254962225/70368744177664), (-856763197/140737488355328)), (41/70368744177664), by norm_num⟩
  | 12 => ⟨((330755721/562949953421312), (555728067/562949953421312)), (27/281474976710656), by norm_num⟩
  | 13 => ⟨((-396074409/4503599627370496), (-1330950013/9007199254740992)), (131/9007199254740992), by norm_num⟩
  | 14 => ⟨((440414407/36028797018963968), (92496755/4503599627370496)), (37/18014398509481984), by norm_num⟩
  | 15 => ⟨((-57133791/36028797018963968), (-383979465/144115188075855872)), (79/288230376151711744), by norm_num⟩
  | 16 => ⟨((444708895/2305843009213693952), (373594769/1152921504606846976)), (39/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (673405817033/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222422350914325/79228162514264337593543950336), (1594923936671/633825300114114700748351602688)), (46179/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945214000939849/19807040628566084398385987584), (448505744955/9903520314283042199192993792)), (51957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472561447493189/618970019642690137449562112), (1861155195/2417851639229258349412352)), (55209/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771911848603441/154742504910672534362390528), (29772745299/2417851639229258349412352)), (3451/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775114655629821/4835703278458516698824704), (892987316857/4835703278458516698824704)), (12943/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259379881077617/604462909807314587353088), (781168909409/302231454903657293676544)), (11327/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888752360919497/75557863725914323419136), (634516985445/18889465931478580854784)), (36819/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298259357598371/4722366482869645213696), (118931970535/295147905179352825856)), (6905/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622437442198021/590295810358705651712), (1307732336973/295147905179352825856)), (75973/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824710466261009/73786976294838206464), (3267773511999/73786976294838206464)), (47497/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912023046737195/4611686018427387904), (3674104986435/9223372036854775808)), (53453/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595293183971231/1152921504606846976), (917857847401/288230376151711744)), (106955/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298930769916863/36028797018963968), (3209496966307/144115188075855872)), (93639/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493347699070195/36028797018963968), (1202060047117/9007199254740992)), (140567/36028797018963968), by norm_num⟩
  | 3 => ⟨((745695000849825/4503599627370496), (2999901964543/4503599627370496)), (175899/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116098055020927/2251799813685248), (5984085243041/2251799813685248)), (176183/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222434383771029/2251799813685248), (8936921237029/1125899906842624)), (264989/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096614769949345/1125899906842624), (17717555527095/1125899906842624)), (532843/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096614769949345/1125899906842624), (17717555527095/1125899906842624)), (2032634739402389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2135625084593327/2251799813685248), (34513428698819/1125899906842624)), (2109475/2251799813685248), by norm_num⟩
  | 2 => ⟨((3951812657407/4398046511104), (65465627660651/1125899906842624)), (4130615/2251799813685248), by norm_num⟩
  | 3 => ⟨((905212244738085/1125899906842624), (3676460323937/35184372088832)), (3951691/1125899906842624), by norm_num⟩
  | 4 => ⟨((715488517196011/1125899906842624), (189173585029125/1125899906842624)), (7180075/1125899906842624), by norm_num⟩
  | 5 => ⟨((845789523691875/2251799813685248), (480865224421983/2251799813685248)), (23076801/2251799813685248), by norm_num⟩
  | 6 => ⟨((429992534315215/4503599627370496), (722463456390897/4503599627370496)), (54383073/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-360277001/8388608)), (1/33554432), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1539999085/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-251609450301947/4503599627370496), (-1411544604483219/9007199254740992)), (260208697/9007199254740992), by norm_num⟩
  | 1 => ⟨((498969215/4294967296), (174953013/536870912)), (261/4294967296), by norm_num⟩
  | 2 => ⟨((-518788657/4294967296), (-363804563/1073741824)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((359596895/4294967296), (1008680429/4294967296)), (3/67108864), by norm_num⟩
  | 4 => ⟨((-373880361/8589934592), (-1048745993/8589934592)), (101/4294967296), by norm_num⟩
  | 5 => ⟨((155492471/8589934592), (436161197/8589934592)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((-3368099/536870912), (-4723811/268435456)), (119/34359738368), by norm_num⟩
  | 7 => ⟨((512275381/274877906944), (1436948309/274877906944)), (143/137438953472), by norm_num⟩
  | 8 => ⟨((-266311677/549755813888), (-373506251/274877906944)), (75/274877906944), by norm_num⟩
  | 9 => ⟨((246124251/2199023255552), (345193073/1099511627776)), (35/549755813888), by norm_num⟩
  | 10 => ⟨((-204720397/8796093022208), (-574247053/8796093022208)), (59/4398046511104), by norm_num⟩
  | 11 => ⟨((77400745/17592186044416), (868445947/70368744177664)), (45/17592186044416), by norm_num⟩
  | 12 => ⟨((-429200865/562949953421312), (-1203921719/562949953421312)), (63/140737488355328), by norm_num⟩
  | 13 => ⟨((549229605/4503599627370496), (1540606053/4503599627370496)), (325/4503599627370496), by norm_num⟩
  | 14 => ⟨((-326311673/18014398509481984), (-457657175/9007199254740992)), (195/18014398509481984), by norm_num⟩
  | 15 => ⟨((180945613/72057594037927936), (507558049/72057594037927936)), (109/72057594037927936), by norm_num⟩
  | 16 => ⟨((-11758307/36028797018963968), (-263859323/288230376151711744)), (229/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-155764026301/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779197867180985/633825300114114700748351602688), (-2950786323561/633825300114114700748351602688)), (92491/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890224286468031/39614081257132168796771975168), (-1659551606939/19807040628566084398385987584)), (52035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890029137442965/2475880078570760549798248448), (-3525901008859/2475880078570760549798248448)), (27649/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771694965727619/154742504910672534362390528), (-3525174187657/154742504910672534362390528)), (110621/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550025738972735/9671406556917033397649408), (-3304078685743/9671406556917033397649408)), (103733/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629600755453273/302231454903657293676544), (-722574220905/151115727451828646838272)), (11349/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944231025733367/37778931862957161709568), (-4695285315055/75557863725914323419136)), (147585/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324510306296807/1180591620717411303424), (-110006189743/147573952589676412928)), (27683/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811068430144823/295147905179352825856), (-4838215830557/590295810358705651712)), (152325/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912166882649661/36893488147419103232), (-3022343024385/36893488147419103232)), (190509/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823620968154855/9223372036854775808), (-6796033349761/9223372036854775808)), (3351/144115188075855872), by norm_num⟩
  | 6 => ⟨((1594866390621645/1152921504606846976), (-6790737811161/1152921504606846976)), (107321/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195347762925197/144115188075855872), (-5935941583581/144115188075855872)), (47003/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492780988753013/36028797018963968), (-1111501634269/4503599627370496)), (282419/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490675099480703/9007199254740992), (-693388259253/562949953421312)), (176863/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115373425803127/2251799813685248), (-1382880629151/281474976710656)), (354781/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110106085883189/1125899906842624), (-8258393468293/562949953421312)), (534813/1125899906842624), by norm_num⟩
  | 0 => ⟨((273574209542667/281474976710656), (-32723274888229/1125899906842624)), (1080225/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273574209542667/281474976710656), (-32723274888229/1125899906842624)), (4120731358054732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1062629768454313/1125899906842624), (-31804759932167/562949953421312)), (2162601/1125899906842624), by norm_num⟩
  | 2 => ⟨((1998642769130569/2251799813685248), (-15008742996187/140737488355328)), (2163253/562949953421312), by norm_num⟩
  | 3 => ⟨((1748337365023359/2251799813685248), (-426284652562973/2251799813685248)), (8602991/1125899906842624), by norm_num⟩
  | 4 => ⟨((1276740907186141/2251799813685248), (-330974974632457/1125899906842624)), (33232535/2251799813685248), by norm_num⟩
  | 5 => ⟨((66163164322323/281474976710656), (-375316923644811/1125899906842624)), (3576451/140737488355328), by norm_num⟩
  | 6 => ⟨((-251609450301947/4503599627370496), (-1411544604483219/9007199254740992)), (260208697/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1539999085/33554432)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile021Terms0

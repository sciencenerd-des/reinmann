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
namespace Reinmann.XiBand97.Tile004Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10277/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10277/640))
  have he : value ((69/80), (10277/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1493900685/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((166508138612119/2251799813685248), (613621375158945/1125899906842624)), (728093/35184372088832), by norm_num⟩
  | 1 => ⟨((-220135969/4294967296), (-811252453/2147483648)), (1/67108864), by norm_num⟩
  | 2 => ⟨((76293313/4294967296), (1124634701/8589934592)), (23/4294967296), by norm_num⟩
  | 3 => ⟨((-70509993/17179869184), (-1039383163/34359738368)), (11/8589934592), by norm_num⟩
  | 4 => ⟨((195495211/274877906944), (720445509/137438953472)), (63/274877906944), by norm_num⟩
  | 5 => ⟨((-216811127/2199023255552), (-1597999275/2199023255552)), (9/274877906944), by norm_num⟩
  | 6 => ⟨((200376029/17592186044416), (1476864923/17592186044416)), (69/17592186044416), by norm_num⟩
  | 7 => ⟨((-158731519/140737488355328), (-1169925437/140737488355328)), (57/140737488355328), by norm_num⟩
  | 8 => ⟨((110024305/1125899906842624), (405465259/562949953421312)), (81/2251799813685248), by norm_num⟩
  | 9 => ⟨((-33894683/4503599627370496), (-499639291/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 10 => ⟨((150361625/288230376151711744), (1108235411/288230376151711744)), (15/72057594037927936), by norm_num⟩
  | 11 => ⟨((-37899177/1152921504606846976), (-558669273/2305843009213693952)), (63/4611686018427387904), by norm_num⟩
  | 12 => ⟨((35026277/18446744073709551616), (258160021/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-119524259/1180591620717411303424), (-55059351/73786976294838206464)), (105/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((47341659/9444732965739290427392), (697860277/18889465931478580854784)), (85/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-70004773/302231454903657293676544), (-1031935751/604462909807314587353088)), (65/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((48523611/4835703278458516698824704), (1430566713/19342813113834066795298816)), (23/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (467619071459/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781045800960461/633825300114114700748351602688), (2219006518133/633825300114114700748351602688)), (11553/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236537887345803/4951760157141521099596496896), (2496244062997/39614081257132168796771975168)), (6499/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892237754920219/2475880078570760549798248448), (2652097004313/2475880078570760549798248448)), (13813/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773903447386627/154742504910672534362390528), (165744648885/9671406556917033397649408)), (13815/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552096046102235/9671406556917033397649408), (621493920257/2417851639229258349412352)), (6477/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630506442542615/302231454903657293676544), (2175034650425/604462909807314587353088)), (11337/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891405263173645/75557863725914323419136), (441758423261/9444732965739290427392)), (36855/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650124198133357/2361183241434822606848), (1325116035069/2361183241434822606848)), (27649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812585666864207/295147905179352825856), (1821775755573/295147905179352825856)), (19015/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914063137987311/36893488147419103232), (1138415721071/18446744073709551616)), (47557/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456971685527735/2305843009213693952), (5121802845247/9223372036854775808)), (6691/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599131161624849/1152921504606846976), (5120467662647/1152921504606846976)), (53561/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199078306127347/144115188075855872), (2239453350667/72057594037927936)), (5863/18014398509481984), by norm_num⟩
  | 4 => ⟨((749187266480383/18014398509481984), (3357676994639/18014398509481984)), (35215/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497663038815131/9007199254740992), (8388929506553/9007199254740992)), (88169/9007199254740992), by norm_num⟩
  | 2 => ⟨((561177672043079/1125899906842624), (4190515154433/1125899906842624)), (88365/2251799813685248), by norm_num⟩
  | 1 => ⟨((560281894909663/562949953421312), (12551780980613/1125899906842624)), (8315/70368744177664), by norm_num⟩
  | 0 => ⟨((278787707655733/281474976710656), (25024405565037/1125899906842624)), (67013/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278787707655733/281474976710656), (25024405565037/1125899906842624)), (255634308935069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((551974090508059/562949953421312), (49570990248953/1125899906842624)), (271451/562949953421312), by norm_num⟩
  | 2 => ⟨((1080241943269419/1125899906842624), (48604502215443/562949953421312)), (139055/140737488355328), by norm_num⟩
  | 3 => ⟨((1028042598122211/1125899906842624), (93266944256337/562949953421312)), (1163375/562949953421312), by norm_num⟩
  | 4 => ⟨((453893230552097/562949953421312), (340642684521001/1125899906842624)), (5020013/1125899906842624), by norm_num⟩
  | 5 => ⟨((314432400315213/562949953421312), (137326069219391/281474976710656)), (11132661/1125899906842624), by norm_num⟩
  | 6 => ⟨((166508138612119/2251799813685248), (613621375158945/1125899906842624)), (728093/35184372088832), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1493900685/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1183888283/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((77404298255249/562949953421312), (1632495960538199/4503599627370496)), (59075/2199023255552), by norm_num⟩
  | 1 => ⟨((-162195803/1073741824), (-427598983/1073741824)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((356380605/4294967296), (939530995/4294967296)), (37/2147483648), by norm_num⟩
  | 3 => ⟨((-261016075/8589934592), (-344060099/4294967296)), (111/17179869184), by norm_num⟩
  | 4 => ⟨((573510935/68719476736), (377988653/17179869184)), (125/68719476736), by norm_num⟩
  | 5 => ⟨((-504052929/274877906944), (-664420767/137438953472)), (7/17179869184), by norm_num⟩
  | 6 => ⟨((369172495/1099511627776), (486627213/549755813888)), (21/274877906944), by norm_num⟩
  | 7 => ⟨((-231758537/4398046511104), (-152747039/1099511627776)), (27/2199023255552), by norm_num⟩
  | 8 => ⟨((254612777/35184372088832), (1342478193/70368744177664)), (121/70368744177664), by norm_num⟩
  | 9 => ⟨((-248640645/281474976710656), (-1310989369/562949953421312)), (121/562949953421312), by norm_num⟩
  | 10 => ⟨((437055469/4503599627370496), (1152215225/4503599627370496)), (27/1125899906842624), by norm_num⟩
  | 11 => ⟨((-349203279/36028797018963968), (-920609313/36028797018963968)), (89/36028797018963968), by norm_num⟩
  | 12 => ⟨((511518685/576460752303423488), (674261803/288230376151711744)), (133/576460752303423488), by norm_num⟩
  | 13 => ⟨((-345821977/4611686018427387904), (-455847571/2305843009213693952)), (23/1152921504606846976), by norm_num⟩
  | 14 => ⟨((217099585/36893488147419103232), (143085641/9223372036854775808)), (59/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-508817647/1180591620717411303424), (-1341402825/1180591620717411303424)), (141/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((69874165/2361183241434822606848), (368420407/4722366482869645213696)), (157/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (786937515579/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222563287413423/79228162514264337593543950336), (1866063845277/633825300114114700748351602688)), (2887/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1891696250012639/39614081257132168796771975168), (2099141630557/39614081257132168796771975168)), (12993/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891593085952551/2475880078570760549798248448), (2230122036081/2475880078570760549798248448)), (55227/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886629449867555/77371252455336267181195264), (2229879107927/154742504910672534362390528)), (55235/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193936488946883/1208925819614629174706176), (2090253569779/9671406556917033397649408)), (51791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260484396267513/604462909807314587353088), (1828713799067/604462909807314587353088)), (45325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890546710514801/75557863725914323419136), (2971176075081/75557863725914323419136)), (18417/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299604693228285/4722366482869645213696), (2227958730233/4722366482869645213696)), (55265/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812143292827867/295147905179352825856), (3062755426613/590295810358705651712)), (38005/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827020856273285/73786976294838206464), (1913706338807/36893488147419103232)), (95045/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826643853577713/9223372036854775808), (269026314055/576460752303423488)), (53485/4611686018427387904), by norm_num⟩
  | 6 => ⟨((12483509053399/9007199254740992), (4302648558759/1152921504606846976)), (107027/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598996275042623/72057594037927936), (1881411959739/72057594037927936)), (5857/9007199254740992), by norm_num⟩
  | 4 => ⟨((748373945768947/18014398509481984), (2820124939267/18014398509481984)), (140693/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495633223798081/9007199254740992), (3521669705071/4503599627370496)), (176087/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120330758482819/2251799813685248), (3516442567519/1125899906842624)), (176419/2251799813685248), by norm_num⟩
  | 1 => ⟨((279384995587601/281474976710656), (10523210001691/1125899906842624)), (265457/1125899906842624), by norm_num⟩
  | 0 => ⟨((138644435432031/140737488355328), (20942057321679/1125899906842624)), (267119/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138644435432031/140737488355328), (20942057321679/1125899906842624)), (1018978121043968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1092270555528251/1125899906842624), (2578825787713/70368744177664)), (268115/281474976710656), by norm_num⟩
  | 2 => ⟨((8266668452609/8796093022208), (80057574102621/1125899906842624)), (539865/281474976710656), by norm_num⟩
  | 3 => ⟨((988753452197809/1125899906842624), (150478040774611/1125899906842624)), (2183035/562949953421312), by norm_num⟩
  | 4 => ⟨((848201285632761/1125899906842624), (528592928702165/2251799813685248)), (552221/70368744177664), by norm_num⟩
  | 5 => ⟨((288477153223259/562949953421312), (796435276309571/2251799813685248)), (17460725/1125899906842624), by norm_num⟩
  | 6 => ⟨((77404298255249/562949953421312), (1632495960538199/4503599627370496)), (59075/2199023255552), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1183888283/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1493900685/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-164135350642505/562949953421312), (181495623846105/2251799813685248)), (58228163/2251799813685248), by norm_num⟩
  | 1 => ⟨((867995877/2147483648), (-239950523/2147483648)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-601648895/2147483648), (332642057/4294967296)), (111/4294967296), by norm_num⟩
  | 3 => ⟨((556041647/4294967296), (-307426539/8589934592)), (105/8589934592), by norm_num⟩
  | 4 => ⟨((-96354675/2147483648), (213091839/17179869184)), (37/8589934592), by norm_num⟩
  | 5 => ⟨((854886033/68719476736), (-59081603/17179869184)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((-395041229/137438953472), (436823963/549755813888)), (157/549755813888), by norm_num⟩
  | 7 => ⟨((1251756407/2199023255552), (-346038055/2199023255552)), (127/2199023255552), by norm_num⟩
  | 8 => ⟨((-27114107/274877906944), (119927651/4398046511104)), (45/4398046511104), by norm_num⟩
  | 9 => ⟨((1069173579/70368744177664), (-295564491/70368744177664)), (113/70368744177664), by norm_num⟩
  | 10 => ⟨((-1185751443/562949953421312), (163895755/281474976710656)), (127/562949953421312), by norm_num⟩
  | 11 => ⟨((1195491301/4503599627370496), (-20655251/281474976710656)), (65/2251799813685248), by norm_num⟩
  | 12 => ⟨((-552434283/18014398509481984), (305432085/36028797018963968)), (61/18014398509481984), by norm_num⟩
  | 13 => ⟨((942568039/288230376151711744), (-260565401/288230376151711744)), (53/144115188075855872), by norm_num⟩
  | 14 => ⟨((-746672433/2305843009213693952), (412823253/4611686018427387904)), (85/2305843009213693952), by norm_num⟩
  | 15 => ⟨((1104114969/36893488147419103232), (-305223759/36893488147419103232)), (127/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-382657089/147573952589676412928), (52891247/73786976294838206464)), (89/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (467619071459/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780114527348099/633825300114114700748351602688), (2216822446835/316912650057057350374175801344)), (23159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472813759924611/9903520314283042199192993792), (2493645181993/19807040628566084398385987584)), (26061/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236390464145501/309485009821345068724781056), (2649172981867/1237940039285380274899124224)), (13849/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772788866996511/154742504910672534362390528), (2648807221373/77371252455336267181195264)), (27707/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551050554969315/9671406556917033397649408), (310358510673/604462909807314587353088)), (25985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630048754321473/302231454903657293676544), (543030204483/75557863725914323419136)), (22747/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889916705187535/75557863725914323419136), (7057934514215/75557863725914323419136)), (73963/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299131041090085/4722366482869645213696), (2646087351953/2361183241434822606848)), (3469/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623633449503951/590295810358705651712), (7274665850271/590295810358705651712)), (38185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228275205201731/9223372036854775808), (2272554940473/18446744073709551616)), (95539/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456429599575595/2305843009213693952), (1277776981729/1152921504606846976)), (26897/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798479455249589/576460752303423488), (5108430853007/576460752303423488)), (53861/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197173198049341/144115188075855872), (2233431813045/36028797018963968)), (94407/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495508112628791/36028797018963968), (13388529116423/36028797018963968)), (141911/36028797018963968), by norm_num⟩
  | 3 => ⟨((186758091010267/1125899906842624), (8357267381653/4503599627370496)), (177915/9007199254740992), by norm_num⟩
  | 2 => ⟨((559367094243733/1125899906842624), (16682807923211/2251799813685248)), (89353/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115075235122543/1125899906842624), (24944766590559/1125899906842624)), (33755/140737488355328), by norm_num⟩
  | 0 => ⟨((1103948181016119/1125899906842624), (49570990248953/1125899906842624)), (548027/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103948181016119/1125899906842624), (49570990248953/1125899906842624)), (2090557102683639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080241943269421/1125899906842624), (48604502215443/562949953421312)), (561471/562949953421312), by norm_num⟩
  | 2 => ⟨((1028042598122215/1125899906842624), (93266944256337/562949953421312)), (587179/281474976710656), by norm_num⟩
  | 3 => ⟨((907786461104201/1125899906842624), (170321342260501/562949953421312)), (2533703/562949953421312), by norm_num⟩
  | 4 => ⟨((628864800630437/1125899906842624), (549304276877569/1125899906842624)), (11237763/1125899906842624), by norm_num⟩
  | 5 => ⟨((83254069306067/1125899906842624), (1227242750317923/2251799813685248)), (11759469/562949953421312), by norm_num⟩
  | 6 => ⟨((-164135350642505/562949953421312), (181495623846105/2251799813685248)), (58228163/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1493900685/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-867182493/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((212825967478251/1125899906842624), (-366831428338365/2251799813685248)), (60431203/4503599627370496), by norm_num⟩
  | 1 => ⟨((-81665559/268435456), (140760519/536870912)), (3/134217728), by norm_num⟩
  | 2 => ⟨((1051485175/4294967296), (-56636329/268435456)), (5/268435456), by norm_num⟩
  | 3 => ⟨((-564100035/4294967296), (243073747/2147483648)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((907883983/17179869184), (-48901513/1073741824)), (9/2147483648), by norm_num⟩
  | 5 => ⟨((-584473161/34359738368), (251852637/17179869184)), (3/2147483648), by norm_num⟩
  | 6 => ⟨((313557755/68719476736), (-270227455/68719476736)), (53/137438953472), by norm_num⟩
  | 7 => ⟨((-144186211/137438953472), (497044927/549755813888)), (25/274877906944), by norm_num⟩
  | 8 => ⟨((464117509/2199023255552), (-399981475/2199023255552)), (41/2199023255552), by norm_num⟩
  | 9 => ⟨((-663971835/17592186044416), (572218089/17592186044416)), (15/4398046511104), by norm_num⟩
  | 10 => ⟨((854897155/140737488355328), (-736759589/140737488355328)), (79/140737488355328), by norm_num⟩
  | 11 => ⟨((-1000657377/1125899906842624), (107797165/140737488355328)), (95/1125899906842624), by norm_num⟩
  | 12 => ⟨((1073663947/9007199254740992), (-925295169/9007199254740992)), (13/1125899906842624), by norm_num⟩
  | 13 => ⟨((-1063381823/72057594037927936), (916433923/72057594037927936)), (105/72057594037927936), by norm_num⟩
  | 14 => ⟨((977969727/576460752303423488), (-842824857/576460752303423488)), (99/576460752303423488), by norm_num⟩
  | 15 => ⟨((-419728415/2305843009213693952), (723452949/4611686018427387904)), (87/4611686018427387904), by norm_num⟩
  | 16 => ⟨((84440853/4611686018427387904), (-291088151/18446744073709551616)), (71/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-115820248925/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444956824764819/158456325028528675187087900672), (-1097780259417/633825300114114700748351602688)), (46155/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945466263793039/19807040628566084398385987584), (-1234850446307/39614081257132168796771975168)), (6491/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236347727186803/309485009821345068724781056), (-1311842729703/2475880078570760549798248448)), (55177/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772447841183601/154742504910672534362390528), (-1311633669323/154742504910672534362390528)), (55181/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550731767164321/9671406556917033397649408), (-307358620353/2417851639229258349412352)), (51737/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259819492839377/604462909807314587353088), (-268883284029/151115727451828646838272)), (45275/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944733330166945/37778931862957161709568), (-1747325133291/75557863725914323419136)), (18395/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324698755284973/1180591620717411303424), (-655064883303/2361183241434822606848)), (27597/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623173880349271/590295810358705651712), (-112552311659/36893488147419103232)), (593/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1825630865014159/73786976294838206464), (-70317481465/2305843009213693952)), (94899/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456270334277231/2305843009213693952), (-1265105247407/4611686018427387904)), (106787/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798164085569479/576460752303423488), (-158042985587/72057594037927936)), (26705/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196628404552695/144115188075855872), (-2210889861751/144115188075855872)), (93505/144115188075855872), by norm_num⟩
  | 4 => ⟨((747352553861939/18014398509481984), (-1656456870983/18014398509481984)), (140331/36028797018963968), by norm_num⟩
  | 3 => ⟨((93317859238473/562949953421312), (-516895210497/1125899906842624)), (21943/1125899906842624), by norm_num⟩
  | 2 => ⟨((1117792275057817/2251799813685248), (-4126203621733/2251799813685248)), (351479/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227509385434919/2251799813685248), (-6166954594319/1125899906842624)), (66025/281474976710656), by norm_num⟩
  | 0 => ⟨((550837185559863/562949953421312), (-24489542590247/2251799813685248)), (66271/140737488355328), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550837185559863/562949953421312), (-24489542590247/2251799813685248)), (252803803027105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1077836917991325/1125899906842624), (-47925221892555/2251799813685248)), (2098107/2251799813685248), by norm_num⟩
  | 2 => ⟨((1031315668475297/1125899906842624), (-91758731206543/2251799813685248)), (4106393/2251799813685248), by norm_num⟩
  | 3 => ⟨((1885615382687593/2251799813685248), (-168100586273427/2251799813685248)), (7857513/2251799813685248), by norm_num⟩
  | 4 => ⟨((1566430347353979/2251799813685248), (-281528623805351/2251799813685248)), (14332625/2251799813685248), by norm_num⟩
  | 5 => ⟨((527232850064901/1125899906842624), (-97920556103027/562949953421312)), (11762193/1125899906842624), by norm_num⟩
  | 6 => ⟨((212825967478251/1125899906842624), (-366831428338365/2251799813685248)), (60431203/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-867182493/33554432)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-965419313/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-421964965151993/2251799813685248), (458200050726911/4503599627370496)), (85510277/4503599627370496), by norm_num⟩
  | 1 => ⟨((721034739/2147483648), (-391475811/2147483648)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-1291920821/4294967296), (701430491/4294967296)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((192900947/1073741824), (-418931575/4294967296)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((-691264197/8589934592), (750624617/17179869184)), (151/17179869184), by norm_num⟩
  | 5 => ⟨((990863337/34359738368), (-268987753/17179869184)), (55/17179869184), by norm_num⟩
  | 6 => ⟨((-1183592511/137438953472), (321307569/68719476736)), (133/137438953472), by norm_num⟩
  | 7 => ⟨((1211836051/549755813888), (-82243697/68719476736)), (69/274877906944), by norm_num⟩
  | 8 => ⟨((-33926855/68719476736), (147360923/549755813888)), (125/2199023255552), by norm_num⟩
  | 9 => ⟨((432275653/4398046511104), (-469396141/8796093022208)), (101/8796093022208), by norm_num⟩
  | 10 => ⟨((-154906799/8796093022208), (42052249/4398046511104)), (147/70368744177664), by norm_num⟩
  | 11 => ⟨((807434833/281474976710656), (-54798193/35184372088832)), (97/281474976710656), by norm_num⟩
  | 12 => ⟨((-964486005/2251799813685248), (130913575/562949953421312)), (59/1125899906842624), by norm_num⟩
  | 13 => ⟨((132932841/2251799813685248), (-577392339/18014398509481984)), (33/4503599627370496), by norm_num⟩
  | 14 => ⟨((-1088839665/144115188075855872), (591170395/144115188075855872)), (137/144115188075855872), by norm_num⟩
  | 15 => ⟨((1040500683/1152921504606846976), (-564925415/1152921504606846976)), (33/288230376151711744), by norm_num⟩
  | 16 => ⟨((-233040869/2305843009213693952), (506105231/9223372036854775808)), (15/1152921504606846976), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (430543913411/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779576389450869/633825300114114700748351602688), (2039885468755/316912650057057350374175801344)), (46301/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118165613230575/2475880078570760549798248448), (2294546553953/19807040628566084398385987584)), (26051/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890480867565659/2475880078570760549798248448), (4875139993529/2475880078570760549798248448)), (55373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886073128382155/77371252455336267181195264), (2437136024643/77371252455336267181195264)), (55389/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550448357961527/9671406556917033397649408), (2284353931543/4835703278458516698824704)), (25973/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259570836355527/604462909807314587353088), (1998348602769/302231454903657293676544)), (22735/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((3689572913413/147573952589676412928), (6492903899795/75557863725914323419136)), (36961/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298489921298409/4722366482869645213696), (4868165016683/4722366482869645213696)), (55471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811376288321575/295147905179352825856), (3345634228937/295147905179352825856)), (2385/18446744073709551616), by norm_num⟩
  | 8 => ⟨((28517211732503/1152921504606846976), (261262436757/2305843009213693952)), (5967/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824482171798783/9223372036854775808), (587523586585/576460752303423488)), (6719/576460752303423488), by norm_num⟩
  | 6 => ⟨((797862201804461/576460752303423488), (9394039628065/1152921504606846976)), (107627/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299023734821245/36028797018963968), (8212654932547/144115188075855872)), (11789/18014398509481984), by norm_num⟩
  | 4 => ⟨((186736824312029/4503599627370496), (12304723526055/36028797018963968)), (8859/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492054603992433/9007199254740992), (7677976410577/4503599627370496)), (177665/9007199254740992), by norm_num⟩
  | 2 => ⟨((279183556691767/562949953421312), (7659264243541/1125899906842624)), (89197/1125899906842624), by norm_num⟩
  | 1 => ⟨((556050352522471/562949953421312), (22884243289885/1125899906842624)), (33677/140737488355328), by norm_num⟩
  | 0 => ⟨((549050403425069/562949953421312), (177321730653/4398046511104)), (136539/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549050403425069/562949953421312), (177321730653/4398046511104)), (520854951024913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1069157858964745/1125899906842624), (88547101541791/1125899906842624)), (1109383/1125899906842624), by norm_num⟩
  | 2 => ⟨((1008311601497725/1125899906842624), (168169175477493/1125899906842624)), (570361/281474976710656), by norm_num⟩
  | 3 => ⟨((877885687819215/1125899906842624), (150605688496575/562949953421312)), (1191969/281474976710656), by norm_num⟩
  | 4 => ⟨((603921346040887/1125899906842624), (117430135335985/281474976710656)), (9986303/1125899906842624), by norm_num⟩
  | 5 => ⟨((127971948809773/1125899906842624), (1007813429479705/2251799813685248)), (19045589/1125899906842624), by norm_num⟩
  | 6 => ⟨((-421964965151993/2251799813685248), (458200050726911/4503599627370496)), (85510277/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-965419313/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1048477361/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((828783194764693/4503599627370496), (282598241061253/9007199254740992)), (15090941/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1538026457/4294967296), (-32777237/536870912)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((748215323/2147483648), (255126233/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-970639861/4294967296), (-82742121/2147483648)), (75/4294967296), by norm_num⟩
  | 4 => ⟨((472194489/4294967296), (161008733/8589934592)), (37/4294967296), by norm_num⟩
  | 5 => ⟨((-735078439/17179869184), (-125323411/17179869184)), (117/34359738368), by norm_num⟩
  | 6 => ⟨((476798865/34359738368), (40644683/17179869184)), (77/68719476736), by norm_num⟩
  | 7 => ⟨((-1060351715/274877906944), (-180779203/274877906944)), (87/274877906944), by norm_num⟩
  | 8 => ⟨((515837291/549755813888), (175890043/1099511627776)), (43/549755813888), by norm_num⟩
  | 9 => ⟨((-1784485369/8796093022208), (-9507395/274877906944)), (151/8796093022208), by norm_num⟩
  | 10 => ⟨((347244819/8796093022208), (118403433/17592186044416)), (119/35184372088832), by norm_num⟩
  | 11 => ⟨((-491423431/70368744177664), (-41891353/35184372088832)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((1275021123/1125899906842624), (217378157/1125899906842624)), (113/1125899906842624), by norm_num⟩
  | 13 => ⟨((-1526816335/9007199254740992), (-65076671/2251799813685248)), (137/9007199254740992), by norm_num⟩
  | 14 => ⟨((1697741373/72057594037927936), (72361917/18014398509481984)), (77/36028797018963968), by norm_num⟩
  | 15 => ⟨((-1761947823/576460752303423488), (-37549277/72057594037927936)), (81/288230376151711744), by norm_num⟩
  | 16 => ⟨((428574019/1152921504606846976), (292270077/4611686018427387904)), (5/144115188075855872), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (219967088857/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444845032728649/158456325028528675187087900672), (8140308155/19807040628566084398385987584)), (46113/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890429567146507/39614081257132168796771975168), (293007794263/39614081257132168796771975168)), (25939/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890247550511103/2475880078570760549798248448), (77816870615/618970019642690137449562112)), (55121/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442978429673713/38685626227668133590597632), (311207538553/154742504910672534362390528)), (110245/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550231180810597/9671406556917033397649408), (145846696643/4835703278458516698824704)), (103357/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314845408301897/151115727451828646838272), (31896007919/75557863725914323419136)), (11305/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944377712999629/37778931862957161709568), (414528787317/75557863725914323419136)), (18371/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((20285341357815/73786976294838206464), (310792228241/4722366482869645213696)), (55115/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622441174269429/590295810358705651712), (213584899071/295147905179352825856)), (37893/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824715594803769/73786976294838206464), (133427025441/18446744073709551616)), (189475/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456013124893145/2305843009213693952), (600072371117/9223372036854775808)), (53293/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595300384538515/1152921504606846976), (599636127597/1152921504606846976)), (53297/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195730272375273/144115188075855872), (131047816137/36028797018963968)), (186557/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493360268644353/36028797018963968), (392653634383/18014398509481984)), (4373/562949953421312), by norm_num⟩
  | 3 => ⟨((1491408820779937/9007199254740992), (122490266613/1125899906842624)), (21869/562949953421312), by norm_num⟩
  | 2 => ⟨((2232243034475473/4503599627370496), (977358988491/2251799813685248)), (349999/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222527863700489/2251799813685248), (2919294677347/2251799813685248)), (525241/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096754070515331/1125899906842624), (5787660308871/2251799813685248)), (1051465/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096754070515331/1125899906842624), (5787660308871/2251799813685248)), (4011020664695357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1068355285961595/1125899906842624), (11275673732517/2251799813685248)), (4107795/2251799813685248), by norm_num⟩
  | 2 => ⟨((1013723533416267/1125899906842624), (2674843820863/281474976710656)), (244901/70368744177664), by norm_num⟩
  | 3 => ⟨((1825243823764043/2251799813685248), (38533473363911/2251799813685248)), (14261003/2251799813685248), by norm_num⟩
  | 4 => ⟨((739415237398355/1125899906842624), (62468238817863/2251799813685248)), (2950899/281474976710656), by norm_num⟩
  | 5 => ⟨((1938926612444953/4503599627370496), (82049864920761/2251799813685248)), (32317025/2251799813685248), by norm_num⟩
  | 6 => ⟨((828783194764693/4503599627370496), (282598241061253/9007199254740992)), (15090941/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1048477361/33554432)), (1/16777216), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-560212757/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-294927354734871/4503599627370496), (-86099480392029/562949953421312)), (32860261/1125899906842624), by norm_num⟩
  | 1 => ⟨((73109173/536870912), (682978959/2147483648)), (263/4294967296), by norm_num⟩
  | 2 => ⟨((-304052503/2147483648), (-355053705/1073741824)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((210753135/2147483648), (492208949/2147483648)), (195/4294967296), by norm_num⟩
  | 4 => ⟨((-54781103/1073741824), (-127939967/1073741824)), (205/8589934592), by norm_num⟩
  | 5 => ⟨((91131281/4294967296), (851339783/17179869184)), (43/4294967296), by norm_num⟩
  | 6 => ⟨((-126334781/17179869184), (-1180207541/68719476736)), (241/68719476736), by norm_num⟩
  | 7 => ⟨((600470381/274877906944), (87649021/17179869184)), (289/274877906944), by norm_num⟩
  | 8 => ⟨((-624321527/1099511627776), (-1458088123/1099511627776)), (303/1099511627776), by norm_num⟩
  | 9 => ⟨((72124451/549755813888), (673779781/2199023255552)), (283/4398046511104), by norm_num⟩
  | 10 => ⟨((-479931455/17592186044416), (-1120868533/17592186044416)), (119/8796093022208), by norm_num⟩
  | 11 => ⟨((181452619/35184372088832), (423778289/35184372088832)), (91/35184372088832), by norm_num⟩
  | 12 => ⟨((-503093485/562949953421312), (-1174962905/562949953421312)), (255/562949953421312), by norm_num⟩
  | 13 => ⟨((160946691/1125899906842624), (1503548723/4503599627370496)), (329/4503599627370496), by norm_num⟩
  | 14 => ⟨((-382490555/18014398509481984), (-893297621/18014398509481984)), (99/9007199254740992), by norm_num⟩
  | 15 => ⟨((26512225/9007199254740992), (247674691/36028797018963968)), (111/72057594037927936), by norm_num⟩
  | 16 => ⟨((-27565311/72057594037927936), (-1030050083/1152921504606846976)), (233/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-2573121536083/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889598779988363/316912650057057350374175801344), (-1523284134069/316912650057057350374175801344)), (23125/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945111961638581/19807040628566084398385987584), (-428355007471/4951760157141521099596496896)), (52041/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890028728950685/2475880078570760549798248448), (-3640350363599/2475880078570760549798248448)), (110609/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885847265911971/77371252455336267181195264), (-1819799931361/77371252455336267181195264)), (55317/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550025305203325/9671406556917033397649408), (-426415949421/1208925819614629174706176)), (51873/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78700069024397/37778931862957161709568), (-2984114517553/604462909807314587353088)), (90805/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888461340348577/75557863725914323419136), (-1211922947211/18889465931478580854784)), (147607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298040647671007/4722366482869645213696), (-3634461640831/4722366482869645213696)), (110749/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811067997241453/295147905179352825856), (-4995261142941/590295810358705651712)), (152351/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824332575574603/73786976294838206464), (-6240892038241/73786976294838206464)), (190545/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823619482137777/9223372036854775808), (-3508313339621/4611686018427387904)), (107255/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594864720417495/1152921504606846976), (-1752789527433/288230376151711744)), (107347/576460752303423488), by norm_num⟩
  | 5 => ⟨((149418261834519/18014398509481984), (-6128614657847/144115188075855872)), (5877/4503599627370496), by norm_num⟩
  | 4 => ⟨((746389036856401/18014398509481984), (-4590316622349/18014398509481984)), (141255/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490670735703203/9007199254740992), (-11454305692389/9007199254740992)), (176931/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115367986432229/2251799813685248), (-11422115787413/2251799813685248)), (354951/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110095253118477/1125899906842624), (-17052835123613/1125899906842624)), (535155/1125899906842624), by norm_num⟩
  | 0 => ⟨((273566142307671/281474976710656), (-2111570871965/70368744177664)), (540627/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273566142307671/281474976710656), (-2111570871965/70368744177664)), (2062328340770530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((265626079398173/281474976710656), (-32835845198219/562949953421312)), (1083319/562949953421312), by norm_num⟩
  | 2 => ⟨((1997695616011417/2251799813685248), (-61973941169869/562949953421312)), (8684073/2251799813685248), by norm_num⟩
  | 3 => ⟨((1744975481481431/2251799813685248), (-439843967761521/2251799813685248)), (17320261/2251799813685248), by norm_num⟩
  | 4 => ⟨((633155020634025/1125899906842624), (-681691982348343/2251799813685248)), (8402533/562949953421312), by norm_num⟩
  | 5 => ⟨((252872647669883/1125899906842624), (-766705279086847/2251799813685248)), (58151357/2251799813685248), by norm_num⟩
  | 6 => ⟨((-294927354734871/4503599627370496), (-86099480392029/562949953421312)), (32860261/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-560212757/16777216)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile004Terms0

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
namespace Reinmann.XiBand97.Tile007Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11351/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11351/640))
  have he : value ((69/80), (11351/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-412505271/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((149087849505985/281474976710656), (83407796672263/562949953421312)), (23911545/2251799813685248), by norm_num⟩
  | 1 => ⟨((-788420277/2147483648), (-441084893/4294967296)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((136622823/1073741824), (152868375/4294967296)), (25/8589934592), by norm_num⟩
  | 3 => ⟨((-1010130395/34359738368), (-282560755/34359738368)), (25/34359738368), by norm_num⟩
  | 4 => ⟨((1400338071/274877906944), (391712381/274877906944)), (37/274877906944), by norm_num⟩
  | 5 => ⟨((-1553024617/2199023255552), (-108605733/549755813888)), (43/2199023255552), by norm_num⟩
  | 6 => ⟨((1435299513/17592186044416), (401492041/17592186044416)), (21/8796093022208), by norm_num⟩
  | 7 => ⟨((-1136998641/140737488355328), (-159024615/70368744177664)), (35/140737488355328), by norm_num⟩
  | 8 => ⟨((1576214805/2251799813685248), (220454927/1125899906842624)), (51/2251799813685248), by norm_num⟩
  | 9 => ⟨((-242788633/4503599627370496), (-271658153/18014398509481984)), (33/18014398509481984), by norm_num⟩
  | 10 => ⟨((1077044841/288230376151711744), (301278533/288230376151711744)), (39/288230376151711744), by norm_num⟩
  | 11 => ⟨((-542945887/2305843009213693952), (-303753259/4611686018427387904)), (41/4611686018427387904), by norm_num⟩
  | 12 => ⟨((1003577095/73786976294838206464), (70181905/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-856155857/1180591620717411303424), (-119744959/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 14 => ⟨((1356438899/37778931862957161709568), (189716299/18889465931478580854784)), (59/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-1002892585/604462909807314587353088), (-280536145/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1390304335/19342813113834066795298816), (97226419/4835703278458516698824704)), (65/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (88823636495/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111315520579381/39614081257132168796771975168), (421497411839/633825300114114700748351602688)), (23061/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892306096705825/39614081257132168796771975168), (237079498789/19807040628566084398385987584)), (25945/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892241127325297/2475880078570760549798248448), (251881593231/1237940039285380274899124224)), (27567/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773907030238373/154742504910672534362390528), (125932149323/38685626227668133590597632)), (27567/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552099628584241/9671406556917033397649408), (472208812099/9671406556917033397649408)), (12923/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630508121634631/302231454903657293676544), (413145966247/604462909807314587353088)), (2827/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472852784802501/18889465931478580854784), (83911663375/9444732965739290427392)), (2297/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((650126584904833/2361183241434822606848), (503409710601/4722366482869645213696)), (13783/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812589246376907/295147905179352825856), (346045213963/295147905179352825856)), (37905/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828136117539881/73786976294838206464), (54060385827/4611686018427387904)), (47385/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114243690057845/576460752303423488), (60805315623/576460752303423488)), (53313/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599144993471025/1152921504606846976), (972632741137/1152921504606846976)), (53319/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299773033143315/36028797018963968), (850769883287/144115188075855872)), (46661/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498398717090585/36028797018963968), (159448437503/4503599627370496)), (35003/18014398509481984), by norm_num⟩
  | 3 => ⟨((748849645354483/4503599627370496), (796746009337/4503599627370496)), (87531/9007199254740992), by norm_num⟩
  | 2 => ⟨((2244801232854573/4503599627370496), (398001102049/562949953421312)), (175137/4503599627370496), by norm_num⟩
  | 1 => ⟨((2241308413849665/2251799813685248), (4768581636913/2251799813685248)), (65723/562949953421312), by norm_num⟩
  | 0 => ⟨((2230842888138417/2251799813685248), (2376868920511/562949953421312)), (526533/2251799813685248), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2230842888138417/2251799813685248), (2376868920511/562949953421312)), (2008564003951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1105020430594885/1125899906842624), (9418992034965/1125899906842624)), (32741/70368744177664), by norm_num⟩
  | 2 => ⟨((1084449361085005/1125899906842624), (4622159825661/281474976710656)), (129631/140737488355328), by norm_num⟩
  | 3 => ⟨((2088442462476813/2251799813685248), (71231884671915/2251799813685248)), (2031797/1125899906842624), by norm_num⟩
  | 4 => ⟨((967341304321479/1125899906842624), (66064350714913/1125899906842624)), (3897345/1125899906842624), by norm_num⟩
  | 5 => ⟨((413617895760775/562949953421312), (227042474384531/2251799813685248)), (3577173/562949953421312), by norm_num⟩
  | 6 => ⟨((149087849505985/281474976710656), (83407796672263/562949953421312)), (23911545/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-412505271/33554432)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-326902693/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((702637080079087/2251799813685248), (-259048598338933/1125899906842624)), (44401163/2251799813685248), by norm_num⟩
  | 1 => ⟨((-46010359/134217728), (271409963/1073741824)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((808760733/4294967296), (-596348641/4294967296)), (7/536870912), by norm_num⟩
  | 3 => ⟨((-1184685973/17179869184), (873541261/17179869184)), (85/17179869184), by norm_num⟩
  | 4 => ⟨((162688821/8589934592), (-239920791/17179869184)), (49/34359738368), by norm_num⟩
  | 5 => ⟨((-1143884403/274877906944), (421727887/137438953472)), (89/274877906944), by norm_num⟩
  | 6 => ⟨((209447577/274877906944), (-617753919/1099511627776)), (67/1099511627776), by norm_num⟩
  | 7 => ⟨((-1051893403/8796093022208), (775625197/8796093022208)), (87/8796093022208), by norm_num⟩
  | 8 => ⟨((1155623019/70368744177664), (-852111373/70368744177664)), (49/35184372088832), by norm_num⟩
  | 9 => ⟨((-564258511/281474976710656), (832124467/562949953421312)), (99/562949953421312), by norm_num⟩
  | 10 => ⟨((991842135/4503599627370496), (-182836433/1125899906842624)), (89/4503599627370496), by norm_num⟩
  | 11 => ⟨((-792472697/36028797018963968), (584338479/36028797018963968)), (73/36028797018963968), by norm_num⟩
  | 12 => ⟨((1160826991/576460752303423488), (-855948579/576460752303423488)), (55/288230376151711744), by norm_num⟩
  | 13 => ⟨((-196199815/1152921504606846976), (289340193/2305843009213693952)), (19/1152921504606846976), by norm_num⟩
  | 14 => ⟨((985360127/73786976294838206464), (-90820769/9223372036854775808)), (49/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-72168583/73786976294838206464), (212857201/295147905179352825856)), (59/590295810358705651712), by norm_num⟩
  | 16 => ⟨((634282337/9444732965739290427392), (-233847537/4722366482869645213696)), (67/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-413815604085/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780507642844145/633825300114114700748351602688), (-981280371195/633825300114114700748351602688)), (46149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891697841732839/39614081257132168796771975168), (-1103846494447/39614081257132168796771975168)), (51921/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891594876409183/2475880078570760549798248448), (-1172723444823/2475880078570760549798248448)), (55169/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773260801819033/154742504910672534362390528), (-1172595822829/154742504910672534362390528)), (55173/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551493813348241/9671406556917033397649408), (-1099173002267/9671406556917033397649408)), (51729/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630243089424871/302231454903657293676544), (-240410203543/151115727451828646838272)), (11317/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890549829373545/75557863725914323419136), (-781206091377/37778931862957161709568)), (73567/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649803613341109/2361183241434822606848), (-1171586804313/4722366482869645213696)), (27591/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406072596188485/147573952589676412928), (-100660665011/36893488147419103232)), (75887/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913513039137159/36893488147419103232), (-1006335803879/36893488147419103232)), (23719/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228331297305145/1152921504606846976), (-2263510944699/9223372036854775808)), (53379/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597896495680483/1152921504606846976), (-282822562093/144115188075855872)), (26697/288230376151711744), by norm_num⟩
  | 5 => ⟨((149749985299975/18014398509481984), (-1978711619997/144115188075855872)), (93473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496760712898343/36028797018963968), (-185373493659/2251799813685248)), (140275/36028797018963968), by norm_num⟩
  | 3 => ⟨((46739138608429/281474976710656), (-1851906081131/4503599627370496)), (43865/2251799813685248), by norm_num⟩
  | 2 => ⟨((2240709474902739/4503599627370496), (-7396661062983/4503599627370496)), (351267/4503599627370496), by norm_num⟩
  | 1 => ⟨((558793916761817/562949953421312), (-5533808983077/1125899906842624)), (527773/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218597007701389/2251799813685248), (-11012974191263/1125899906842624)), (1059043/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218597007701389/2251799813685248), (-11012974191263/1125899906842624)), (4039928444869231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2185668330847171/2251799813685248), (-43402351200379/2251799813685248)), (1053787/1125899906842624), by norm_num⟩
  | 2 => ⟨((2120642456472827/2251799813685248), (-84255397772437/2251799813685248)), (2086301/1125899906842624), by norm_num⟩
  | 3 => ⟨((1993971857024463/2251799813685248), (-158695788690753/2251799813685248)), (4085693/1125899906842624), by norm_num⟩
  | 4 => ⟨((1754480744356981/2251799813685248), (-17565667613665/140737488355328)), (7811653/1125899906842624), by norm_num⟩
  | 5 => ⟨((332979554659019/562949953421312), (-218979505390495/1125899906842624)), (28245611/2251799813685248), by norm_num⟩
  | 6 => ⟨((702637080079087/2251799813685248), (-259048598338933/1125899906842624)), (44401163/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-326902693/16777216)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-412505271/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1164606358877807/4503599627370496), (353426487376391/2251799813685248)), (65442877/4503599627370496), by norm_num⟩
  | 1 => ⟨((-384923751/1073741824), (-116813933/536870912)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((1067235251/4294967296), (647753987/4294967296)), (65/4294967296), by norm_num⟩
  | 3 => ⟨((-986334807/8589934592), (-74831475/1073741824)), (31/4294967296), by norm_num⟩
  | 4 => ⟨((683675191/17179869184), (414953807/17179869184)), (45/17179869184), by norm_num⟩
  | 5 => ⟨((-379110025/34359738368), (-230099249/34359738368)), (13/17179869184), by norm_num⟩
  | 6 => ⟨((87593015/34359738368), (212656861/137438953472)), (25/137438953472), by norm_num⟩
  | 7 => ⟨((-1110214425/2199023255552), (-673840017/2199023255552)), (41/1099511627776), by norm_num⟩
  | 8 => ⟨((769541999/8796093022208), (116767577/2199023255552)), (59/8796093022208), by norm_num⟩
  | 9 => ⟨((-948277097/70368744177664), (-287776415/35184372088832)), (75/70368744177664), by norm_num⟩
  | 10 => ⟨((525836477/281474976710656), (319154257/281474976710656)), (85/562949953421312), by norm_num⟩
  | 11 => ⟨((-1060311481/4503599627370496), (-40221977/281474976710656)), (11/562949953421312), by norm_num⟩
  | 12 => ⟨((979935885/36028797018963968), (594767999/36028797018963968)), (83/36028797018963968), by norm_num⟩
  | 13 => ⟨((-835987441/288230376151711744), (-507399091/288230376151711744)), (9/36028797018963968), by norm_num⟩
  | 14 => ⟨((1324485343/4611686018427387904), (100486357/576460752303423488)), (117/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-244816875/9223372036854775808), (-297181163/18446744073709551616)), (11/4611686018427387904), by norm_num⟩
  | 16 => ⟨((678776507/295147905179352825856), (411980571/295147905179352825856)), (63/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (710589091959/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111257790036665/39614081257132168796771975168), (842165100653/633825300114114700748351602688)), (46143/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945633506871443/19807040628566084398385987584), (947334727685/39614081257132168796771975168)), (51913/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891137181750175/2475880078570760549798248448), (1006420320675/2475880078570760549798248448)), (6895/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772803174740375/154742504910672534362390528), (503141082121/77371252455336267181195264)), (55163/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551064859755325/9671406556917033397649408), (471621381387/4835703278458516698824704)), (6465/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630055458118561/302231454903657293676544), (412595339677/302231454903657293676544)), (22629/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889940162191949/75557863725914323419136), (670329889915/37778931862957161709568)), (73551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299150094013643/4722366482869645213696), (1005254204769/4722366482869645213696)), (27585/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623662018577417/590295810358705651712), (690916809821/295147905179352825856)), (18967/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826240907333187/73786976294838206464), (1726705852629/73786976294838206464)), (94849/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912883727658371/4611686018427387904), (970869208059/4611686018427387904)), (53363/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399253516270081/288230376151711744), (1940731808269/1152921504606846976)), (106751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197228309431033/144115188075855872), (1697008554325/144115188075855872)), (93435/144115188075855872), by norm_num⟩
  | 4 => ⟨((373901115087411/9007199254740992), (2543250914519/36028797018963968)), (70105/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494209055273687/9007199254740992), (793777243317/2251799813685248)), (87681/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237828514611809/4503599627370496), (3169184331565/2251799813685248)), (351023/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115434352295133/1125899906842624), (9477981269467/2251799813685248)), (263643/1125899906842624), by norm_num⟩
  | 0 => ⟨((2210040861189769/2251799813685248), (9418992034965/1125899906842624)), (1057589/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210040861189769/2251799813685248), (9418992034965/1125899906842624)), (4034381875045012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((271112340271251/281474976710656), (4622159825661/281474976710656)), (2093649/2251799813685248), by norm_num⟩
  | 2 => ⟨((1044221231238405/1125899906842624), (71231884671915/2251799813685248)), (2050951/1125899906842624), by norm_num⟩
  | 3 => ⟨((241835326080369/281474976710656), (66064350714913/1125899906842624)), (7868171/2251799813685248), by norm_num⟩
  | 4 => ⟨((1654471583043089/2251799813685248), (113521237192265/1125899906842624)), (14443581/2251799813685248), by norm_num⟩
  | 5 => ⟨((149087849505983/281474976710656), (41703898336131/281474976710656)), (24136961/2251799813685248), by norm_num⟩
  | 6 => ⟨((1164606358877807/4503599627370496), (353426487376391/2251799813685248)), (65442877/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-412505271/16777216)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-478903789/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-33841922948891/140737488355328), (300361614298767/4503599627370496)), (96376187/4503599627370496), by norm_num⟩
  | 1 => ⟨((831092435/2147483648), (-461018915/4294967296)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-668795837/2147483648), (92747665/1073741824)), (61/2147483648), by norm_num⟩
  | 3 => ⟨((1435180501/8589934592), (-199028811/4294967296)), (133/8589934592), by norm_num⟩
  | 4 => ⟨((-1154916955/17179869184), (160162257/8589934592)), (109/17179869184), by norm_num⟩
  | 5 => ⟨((1487013707/68719476736), (-206216967/34359738368)), (71/34359738368), by norm_num⟩
  | 6 => ⟨((-797752079/137438953472), (110631135/68719476736)), (77/137438953472), by norm_num⟩
  | 7 => ⟨((1467351361/1099511627776), (-406980441/1099511627776)), (143/1099511627776), by norm_num⟩
  | 8 => ⟨((-73800341/274877906944), (81876219/1099511627776)), (117/4398046511104), by norm_num⟩
  | 9 => ⟨((844636919/17592186044416), (-234266117/17592186044416)), (85/17592186044416), by norm_num⟩
  | 10 => ⟨((-33984767/4398046511104), (37703677/17592186044416)), (111/140737488355328), by norm_num⟩
  | 11 => ⟨((1272933759/1125899906842624), (-176528661/562949953421312)), (33/281474976710656), by norm_num⟩
  | 12 => ⟨((-1365805235/9007199254740992), (378815893/9007199254740992)), (143/9007199254740992), by norm_num⟩
  | 13 => ⟨((676362685/36028797018963968), (-375188099/72057594037927936)), (9/4503599627370496), by norm_num⟩
  | 14 => ⟨((-1244072855/576460752303423488), (345052543/576460752303423488)), (67/288230376151711744), by norm_num⟩
  | 15 => ⟨((1067870943/4611686018427387904), (-296181677/4611686018427387904)), (117/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-859335991/36893488147419103232), (119171505/18446744073709551616)), (3/1152921504606846976), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (3739845347901/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779817457108047/633825300114114700748351602688), (1107731709887/158456325028528675187087900672)), (23159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890920880294409/39614081257132168796771975168), (4984150193915/39614081257132168796771975168)), (26061/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472692179191621/618970019642690137449562112), (2647453031851/1237940039285380274899124224)), (13849/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772433924627189/154742504910672534362390528), (5294058173341/154742504910672534362390528)), (27707/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550717853945899/9671406556917033397649408), (4962278575595/9671406556917033397649408)), (25985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259806452743467/604462909807314587353088), (2170546351737/302231454903657293676544)), (45493/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944721923629101/37778931862957161709568), (1763146496735/18889465931478580854784)), (36981/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162347061520523/590295810358705651712), (165248776699/147573952589676412928)), (3469/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811573049259501/295147905179352825856), (7268543042547/590295810358705651712)), (76369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825592683899363/73786976294838206464), (2270518374045/18446744073709551616)), (95539/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825033639064167/9223372036854775808), (10212374400727/9223372036854775808)), (26897/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199534318726451/144115188075855872), (5103087538111/576460752303423488)), (107721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74785926995737/9007199254740992), (1115428367395/18014398509481984)), (47203/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494611465199735/36028797018963968), (13371182904657/36028797018963968)), (70955/18014398509481984), by norm_num⟩
  | 3 => ⟨((93309093942889/562949953421312), (16689541839217/9007199254740992)), (88957/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117617352341769/2251799813685248), (2081608069179/281474976710656)), (89353/1125899906842624), by norm_num⟩
  | 1 => ⟨((278351499063057/281474976710656), (24887527262337/1125899906842624)), (33755/140737488355328), by norm_num⟩
  | 0 => ⟨((550317011089081/562949953421312), (49407526046485/1125899906842624)), (548031/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550317011089081/562949953421312), (49407526046485/1125899906842624)), (2090572361472701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1073766983902087/1125899906842624), (96597581699625/1125899906842624)), (1119565/1125899906842624), by norm_num⟩
  | 2 => ⟨((507880157009297/562949953421312), (184249582620029/1125899906842624)), (290945/140737488355328), by norm_num⟩
  | 3 => ⟨((886243173816135/1125899906842624), (332451246798221/1125899906842624)), (2480767/562949953421312), by norm_num⟩
  | 4 => ⟨((1198868793817817/2251799813685248), (1046745439131721/2251799813685248)), (21481817/2251799813685248), by norm_num⟩
  | 5 => ⟨((37926369872113/562949953421312), (1114584373281733/2251799813685248)), (2677851/140737488355328), by norm_num⟩
  | 6 => ⟨((-33841922948891/140737488355328), (300361614298767/4503599627370496)), (96376187/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-478903789/16777216)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1066310657/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((897851208994241/4503599627370496), (-170314576781179/2251799813685248)), (40487017/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1534207731/4294967296), (582051765/4294967296)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((1374465615/4294967296), (-521448381/4294967296)), (65/4294967296), by norm_num⟩
  | 3 => ⟨((-820903927/4294967296), (77859173/1073741824)), (5/536870912), by norm_num⟩
  | 4 => ⟨((1470862385/17179869184), (-279009821/8589934592)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-1054172643/34359738368), (399934791/34359738368)), (27/17179869184), by norm_num⟩
  | 6 => ⟨((1259215877/137438953472), (-477724633/137438953472)), (33/68719476736), by norm_num⟩
  | 7 => ⟨((-80578999/34359738368), (489124363/549755813888)), (69/549755813888), by norm_num⟩
  | 8 => ⟨((288756369/549755813888), (-438196605/2199023255552)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((-919790149/8796093022208), (348952407/8796093022208)), (53/8796093022208), by norm_num⟩
  | 10 => ⟨((164804271/8796093022208), (-31261939/4398046511104)), (39/35184372088832), by norm_num⟩
  | 11 => ⟨((-859024329/281474976710656), (162949455/140737488355328)), (53/281474976710656), by norm_num⟩
  | 12 => ⟨((32065937/70368744177664), (-389288305/2251799813685248)), (65/2251799813685248), by norm_num⟩
  | 13 => ⟨((-565705317/9007199254740992), (429237543/18014398509481984)), (37/9007199254740992), by norm_num⟩
  | 14 => ⟨((1158408981/144115188075855872), (-439480247/144115188075855872)), (39/72057594037927936), by norm_num⟩
  | 15 => ⟨((-1106981473/1152921504606846976), (52496193/144115188075855872)), (77/1152921504606846976), by norm_num⟩
  | 16 => ⟨((247930567/2305843009213693952), (-94060551/2305843009213693952)), (71/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-236168331095/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792558125247/316912650057057350374175801344), (-279737055719/316912650057057350374175801344)), (46129/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472665033813255/9903520314283042199192993792), (-629322438841/39614081257132168796771975168)), (6487/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890492479165509/2475880078570760549798248448), (-334274834671/1237940039285380274899124224)), (27571/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886079295582179/77371252455336267181195264), (-668431100189/154742504910672534362390528)), (6893/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193807586133939/1208925819614629174706176), (-313264102971/4835703278458516698824704)), (12925/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629791196638003/302231454903657293676544), (-548086262609/604462909807314587353088)), (5655/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472270387322323/18889465931478580854784), (-445202075571/37778931862957161709568)), (73519/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324626585391325/1180591620717411303424), (-667596660817/4722366482869645213696)), (6893/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811388597791089/295147905179352825856), (-917610054179/590295810358705651712)), (18957/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825135383301755/73786976294838206464), (-286627441273/18446744073709551616)), (94795/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824524434405137/9223372036854775808), (-644566252049/4611686018427387904)), (53329/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595771910664557/1152921504606846976), (-1288269334711/1152921504606846976)), (106675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598071199195729/72057594037927936), (-563132684271/72057594037927936)), (5835/9007199254740992), by norm_num⟩
  | 4 => ⟨((1493977540106091/36028797018963968), (-1687459368111/36028797018963968)), (140077/36028797018963968), by norm_num⟩
  | 3 => ⟨((46630587715695/281474976710656), (-2105935813873/9007199254740992)), (175163/9007199254740992), by norm_num⟩
  | 2 => ⟨((279222275900991/562949953421312), (-2100861812303/2251799813685248)), (5477/70368744177664), by norm_num⟩
  | 1 => ⟨((2224818659306257/2251799813685248), (-6277275479081/2251799813685248)), (65787/281474976710656), by norm_num⟩
  | 0 => ⟨((2198042089427171/2251799813685248), (-12453670630157/2251799813685248)), (527313/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2198042089427171/2251799813685248), (-12453670630157/2251799813685248)), (2011539463523482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2145498859898431/2251799813685248), (-12156361345527/1125899906842624)), (2070563/2251799813685248), by norm_num⟩
  | 2 => ⟨((255494195208251/281474976710656), (-46329978799771/2251799813685248)), (997587/562949953421312), by norm_num⟩
  | 3 => ⟨((927169384670539/1125899906842624), (-84107232449517/2251799813685248)), (7408261/2251799813685248), by norm_num⟩
  | 4 => ⟨((761945672096657/1125899906842624), (-69261619512205/1125899906842624)), (12754699/2251799813685248), by norm_num⟩
  | 5 => ⟨((1022762381966965/2251799813685248), (-23436182430161/281474976710656)), (18832579/2251799813685248), by norm_num⟩
  | 6 => ⟨((897851208994241/4503599627370496), (-170314576781179/2251799813685248)), (40487017/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1066310657/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1158048703/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-839891658412227/4503599627370496), (-37802480298287/4503599627370496)), (136454743/9007199254740992), by norm_num⟩
  | 1 => ⟨((779320575/2147483648), (35076251/2147483648)), (1/33554432), by norm_num⟩
  | 2 => ⟨((-189560977/536870912), (-68255233/4294967296)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((1967299355/8589934592), (22136425/2147483648)), (165/8589934592), by norm_num⟩
  | 4 => ⟨((-1914093891/17179869184), (-21537747/4294967296)), (81/8589934592), by norm_num⟩
  | 5 => ⟨((372465473/8589934592), (67056833/34359738368)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-1932758251/137438953472), (-10873881/17179869184)), (21/17179869184), by norm_num⟩
  | 7 => ⟨((537281985/137438953472), (48364789/274877906944)), (95/274877906944), by norm_num⟩
  | 8 => ⟨((-261375617/274877906944), (-47056767/1099511627776)), (47/549755813888), by norm_num⟩
  | 9 => ⟨((904201717/4398046511104), (10174249/1099511627776)), (165/8796093022208), by norm_num⟩
  | 10 => ⟨((-703798119/17592186044416), (-31677079/17592186044416)), (65/17592186044416), by norm_num⟩
  | 11 => ⟨((996020293/140737488355328), (11207409/35184372088832)), (93/140737488355328), by norm_num⟩
  | 12 => ⟨((-1292110665/1125899906842624), (-7269537/140737488355328)), (61/562949953421312), by norm_num⟩
  | 13 => ⟨((773640387/4503599627370496), (34820593/4503599627370496)), (37/2251799813685248), by norm_num⟩
  | 14 => ⟨((-860248389/36028797018963968), (-77437423/72057594037927936)), (83/36028797018963968), by norm_num⟩
  | 15 => ⟨((1785563809/576460752303423488), (80366009/576460752303423488)), (87/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1737273369/4611686018427387904), (-19548129/1152921504606846976)), (171/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-4033685801435/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444841992293119/158456325028528675187087900672), (-4776779376561/633825300114114700748351602688)), (46335/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890415184877435/39614081257132168796771975168), (-5373046012103/39614081257132168796771975168)), (52143/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890231374111401/2475880078570760549798248448), (-5707879652857/2475880078570760549798248448)), (55419/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110743533481093/9671406556917033397649408), (-2853387503069/77371252455336267181195264)), (55439/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775107001396833/4835703278458516698824704), (-1337231961225/2417851639229258349412352)), (25997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629682767053815/302231454903657293676544), (-2339569049977/302231454903657293676544)), (11379/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888727263154379/75557863725914323419136), (-7601398517809/75557863725914323419136)), (74003/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162279871813199/590295810358705651712), (-712390377467/590295810358705651712)), (3471/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405601720757087/147573952589676412928), (-1958291114025/147573952589676412928)), (38209/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824668472535161/73786976294838206464), (-9786760749703/73786976294838206464)), (47803/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823993639006155/9223372036854775808), (-1375456252687/1152921504606846976)), (13459/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398808556125329/288230376151711744), (-10995579587535/1152921504606846976)), (13477/144115188075855872), by norm_num⟩
  | 5 => ⟨((597832092466305/72057594037927936), (-9612052013039/144115188075855872)), (94501/144115188075855872), by norm_num⟩
  | 4 => ⟨((746622389436697/18014398509481984), (-3599978898139/9007199254740992)), (35519/9007199254740992), by norm_num⟩
  | 3 => ⟨((93202244526281/562949953421312), (-8984052736365/4503599627370496)), (44541/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115905952333697/2251799813685248), (-1120025794427/140737488355328)), (179019/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110834511774687/1125899906842624), (-13380678107649/562949953421312)), (67667/281474976710656), by norm_num⟩
  | 0 => ⟨((1095474345580519/1125899906842624), (-53045486328671/1125899906842624)), (274965/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095474345580519/1125899906842624), (-53045486328671/1125899906842624)), (1048908235790061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1063371806791143/1125899906842624), (-51612020809967/562949953421312)), (560979/562949953421312), by norm_num⟩
  | 2 => ⟨((994852552968967/1125899906842624), (-97491379983759/562949953421312)), (72657/35184372088832), by norm_num⟩
  | 3 => ⟨((845291237418451/1125899906842624), (-86144023709265/281474976710656)), (4914107/1125899906842624), by norm_num⟩
  | 4 => ⟨((1058326032895809/2251799813685248), (-517394400371593/1125899906842624)), (20773199/2251799813685248), by norm_num⟩
  | 5 => ⟨((43757113276275/4503599627370496), (-1945366403744849/4503599627370496)), (9654653/562949953421312), by norm_num⟩
  | 6 => ⟨((-839891658412227/4503599627370496), (-37802480298287/4503599627370496)), (136454743/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1158048703/33554432)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1237515813/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1024248298395511/9007199254740992), (1093893438870839/9007199254740992)), (172994985/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1015598517/4294967296), (-67790969/268435456)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((527969437/2147483648), (140967357/536870912)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-731921053/4294967296), (-48855563/268435456)), (33/1073741824), by norm_num⟩
  | 4 => ⟨((760993521/8589934592), (406369149/4294967296)), (35/2147483648), by norm_num⟩
  | 5 => ⟨((-79122077/2147483648), (-84502089/2147483648)), (119/17179869184), by norm_num⟩
  | 6 => ⟨((438745957/34359738368), (234289539/17179869184)), (21/8589934592), by norm_num⟩
  | 7 => ⟨((-521340897/137438953472), (-139197543/34359738368)), (51/68719476736), by norm_num⟩
  | 8 => ⟨((542048959/549755813888), (578906307/549755813888)), (27/137438953472), by norm_num⟩
  | 9 => ⟨((-250479805/1099511627776), (-1070046065/4398046511104)), (203/4398046511104), by norm_num⟩
  | 10 => ⟨((833372979/17592186044416), (869179/17179869184)), (171/17592186044416), by norm_num⟩
  | 11 => ⟨((-630163779/70368744177664), (-673012613/70368744177664)), (131/70368744177664), by norm_num⟩
  | 12 => ⟨((873592493/562949953421312), (466496795/281474976710656)), (185/562949953421312), by norm_num⟩
  | 13 => ⟨((-558949083/2251799813685248), (-298477789/1125899906842624)), (15/281474976710656), by norm_num⟩
  | 14 => ⟨((664172539/18014398509481984), (177333461/4503599627370496)), (145/18014398509481984), by norm_num⟩
  | 15 => ⟨((-736590917/144115188075855872), (-786676407/144115188075855872)), (41/36028797018963968), by norm_num⟩
  | 16 => ⟨((191462219/288230376151711744), (102240475/144115188075855872)), (173/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (1065883637939/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444800417985797/158456325028528675187087900672), (315500766611/158456325028528675187087900672)), (92325/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472557196157805/9903520314283042199192993792), (1419529218945/39614081257132168796771975168)), (103873/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59063568646293/77371252455336267181195264), (1507973803563/2475880078570760549798248448)), (55187/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771700339691379/154742504910672534362390528), (753831700703/77371252455336267181195264)), (110385/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550031111275297/9671406556917033397649408), (11039880631/75557863725914323419136)), (103497/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629603272837839/302231454903657293676544), (1236137007395/604462909807314587353088)), (90571/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888470858784807/75557863725914323419136), (1004052397353/37778931862957161709568)), (73599/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298048377826947/4722366482869645213696), (376384546317/1180591620717411303424)), (110417/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811073791732875/295147905179352825856), (1034618607235/295147905179352825856)), (37963/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824348500272819/73786976294838206464), (2585230492505/73786976294838206464)), (189859/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227954921598641/1152921504606846976), (1453287920273/4611686018427387904)), (53413/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594887076484419/1152921504606846976), (2904316867645/1152921504606846976)), (213729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298842106154667/36028797018963968), (2538738122017/144115188075855872)), (187099/144115188075855872), by norm_num⟩
  | 4 => ⟨((746408546194183/18014398509481984), (3803034422251/36028797018963968)), (280819/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490729146408987/9007199254740992), (4744928088845/9007199254740992)), (351325/9007199254740992), by norm_num⟩
  | 2 => ⟨((278860198710327/562949953421312), (591456929041/281474976710656)), (351777/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220480512553117/2251799813685248), (883048498923/140737488355328)), (1057599/2251799813685248), by norm_num⟩
  | 0 => ⟨((1094696519211581/1125899906842624), (27993826160857/2251799813685248)), (2124303/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094696519211581/1125899906842624), (27993826160857/2251799813685248)), (8103572854048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128367803063771/2251799813685248), (54436000698573/2251799813685248)), (2091839/1125899906842624), by norm_num⟩
  | 2 => ⟨((502596434131691/562949953421312), (102904201794729/2251799813685248)), (4055489/1125899906842624), by norm_num⟩
  | 3 => ⟨((1790150931883283/2251799813685248), (183743810848109/2251799813685248)), (15224133/2251799813685248), by norm_num⟩
  | 4 => ⟨((1408152959080411/2251799813685248), (292147776386223/2251799813685248)), (26690505/2251799813685248), by norm_num⟩
  | 5 => ⟨((842679007870607/2251799813685248), (182693307507541/1125899906842624)), (40307213/2251799813685248), by norm_num⟩
  | 6 => ⟨((1024248298395511/9007199254740992), (1093893438870839/9007199254740992)), (172994985/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1237515813/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile007Terms0

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
namespace Reinmann.XiBand97.Tile027Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30399/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30399/1280))
  have he : value ((69/80), (30399/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-69045391/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-903022782819719/2251799813685248), (847584557516545/2251799813685248)), (55044361/1125899906842624), by norm_num⟩
  | 1 => ⟨((18654099/67108864), (-140071117/536870912)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-103440289/1073741824), (776719199/8589934592)), (53/4294967296), by norm_num⟩
  | 3 => ⟨((382396505/17179869184), (-179460241/8589934592)), (25/8589934592), by norm_num⟩
  | 4 => ⟨((-1060228237/274877906944), (995138881/274877906944)), (141/274877906944), by norm_num⟩
  | 5 => ⟨((587915371/1099511627776), (-68977771/137438953472)), (5/68719476736), by norm_num⟩
  | 6 => ⟨((-67918647/1099511627776), (1019983947/17592186044416)), (151/17592186044416), by norm_num⟩
  | 7 => ⟨((215211971/35184372088832), (-403999427/70368744177664)), (61/70368744177664), by norm_num⟩
  | 8 => ⟨((-149173571/281474976710656), (35003883/70368744177664)), (87/1125899906842624), by norm_num⟩
  | 9 => ⟨((367641743/9007199254740992), (-172535771/4503599627370496)), (55/9007199254740992), by norm_num⟩
  | 10 => ⟨((-101931935/36028797018963968), (765393173/288230376151711744)), (31/72057594037927936), by norm_num⟩
  | 11 => ⟨((822153697/4611686018427387904), (-385840087/2305843009213693952)), (127/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-189957839/18446744073709551616), (178295979/18446744073709551616)), (119/73786976294838206464), by norm_num⟩
  | 13 => ⟨((324107669/590295810358705651712), (-304210105/590295810358705651712)), (103/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-1026991163/37778931862957161709568), (963942293/37778931862957161709568)), (165/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((379656549/302231454903657293676544), (-712697475/604462909807314587353088)), (31/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((-526315733/9671406556917033397649408), (988008491/19342813113834066795298816)), (87/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (777610928091/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890520585352631/316912650057057350374175801344), (922504995691/158456325028528675187087900672)), (23141/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892297608448187/39614081257132168796771975168), (4151031752237/39614081257132168796771975168)), (52079/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892231578843879/2475880078570760549798248448), (4410200000165/2475880078570760549798248448)), (55347/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443474221477607/38685626227668133590597632), (2204947358521/77371252455336267181195264)), (27681/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552089485306839/9671406556917033397649408), (1033487951835/2417851639229258349412352)), (25959/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261006735063129/604462909807314587353088), (1808441599619/302231454903657293676544)), (45445/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472848625520661/18889465931478580854784), (1469206552789/18889465931478580854784)), (73877/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650119827119009/2361183241434822606848), (4407086492101/4722366482869645213696)), (27717/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625158223062507/590295810358705651712), (6058876965305/590295810358705651712)), (76265/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57128382896059/2305843009213693952), (7572294774485/73786976294838206464)), (95395/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827864218785919/9223372036854775808), (4258520272133/4611686018427387904)), (6713/576460752303423488), by norm_num⟩
  | 6 => ⟨((1599105830866223/1152921504606846976), (2128699822067/288230376151711744)), (107519/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299763246338731/36028797018963968), (3723962327091/72057594037927936)), (94203/144115188075855872), by norm_num⟩
  | 4 => ⟨((749165122050901/18014398509481984), (2791707317483/9007199254740992)), (141555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497596650571695/9007199254740992), (13949667023027/9007199254740992)), (44345/2251799813685248), by norm_num⟩
  | 2 => ⟨((280568109436035/562949953421312), (6968162802751/1125899906842624)), (178037/2251799813685248), by norm_num⟩
  | 1 => ⟨((70024888409677/70368744177664), (5217751355739/281474976710656)), (134349/562949953421312), by norm_num⟩
  | 0 => ⟨((278663823911029/281474976710656), (20803652356183/562949953421312)), (543981/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278663823911029/281474976710656), (20803652356183/562949953421312)), (2075122837546920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((137748175122137/140737488355328), (41191763364805/562949953421312)), (1117303/1125899906842624), by norm_num⟩
  | 2 => ⟨((536275370106695/562949953421312), (10079208993767/70368744177664)), (2350653/1125899906842624), by norm_num⟩
  | 3 => ⟨((499315226553617/562949953421312), (19203240006203/70368744177664)), (2575965/562949953421312), by norm_num⟩
  | 4 => ⟨((400949979275105/562949953421312), (545041424076131/1125899906842624)), (11950999/1125899906842624), by norm_num⟩
  | 5 => ⟨((307286098401153/1125899906842624), (776389966316765/1125899906842624)), (28594541/1125899906842624), by norm_num⟩
  | 6 => ⟨((-903022782819719/2251799813685248), (847584557516545/2251799813685248)), (55044361/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-69045391/4194304)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-875474845/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((62724314621711/281474976710656), (-357185468014415/1125899906842624)), (26860411/1125899906842624), by norm_num⟩
  | 1 => ⟨((-262869655/1073741824), (1461835/4194304)), (29/1073741824), by norm_num⟩
  | 2 => ⟨((577583667/4294967296), (-411133413/2147483648)), (33/2147483648), by norm_num⟩
  | 3 => ⟨((-846054019/17179869184), (37639685/536870912)), (99/17179869184), by norm_num⟩
  | 4 => ⟨((464742671/34359738368), (-82702841/4294967296)), (7/4294967296), by norm_num⟩
  | 5 => ⟨((-816915215/274877906944), (1162986975/274877906944)), (101/274877906944), by norm_num⟩
  | 6 => ⟨((149578849/274877906944), (-212945297/274877906944)), (19/274877906944), by norm_num⟩
  | 7 => ⟨((-751219025/8796093022208), (1069459749/8796093022208)), (49/4398046511104), by norm_num⟩
  | 8 => ⟨((825298453/70368744177664), (-1174921623/70368744177664)), (111/70368744177664), by norm_num⟩
  | 9 => ⟨((-50371279/35184372088832), (1147362963/562949953421312)), (111/562949953421312), by norm_num⟩
  | 10 => ⟨((354166439/2251799813685248), (-1008405641/4503599627370496)), (25/1125899906842624), by norm_num⟩
  | 11 => ⟨((-565951421/36028797018963968), (805706785/36028797018963968)), (41/18014398509481984), by norm_num⟩
  | 12 => ⟨((829014915/576460752303423488), (-295053125/144115188075855872)), (123/576460752303423488), by norm_num⟩
  | 13 => ⟨((-70058921/576460752303423488), (199476301/1152921504606846976)), (85/4611686018427387904), by norm_num⟩
  | 14 => ⟨((351851847/36893488147419103232), (-500907693/36893488147419103232)), (109/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-824637361/1180591620717411303424), (586990237/590295810358705651712)), (65/590295810358705651712), by norm_num⟩
  | 16 => ⟨((452978369/9444732965739290427392), (-10076167/147573952589676412928)), (73/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-78029885255/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111281686738543/39614081257132168796771975168), (-1480257274235/633825300114114700748351602688)), (23087/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891697065706113/39614081257132168796771975168), (-832573568877/19807040628566084398385987584)), (51949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891594003490227/2475880078570760549798248448), (-442261903079/618970019642690137449562112)), (27601/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773259874477283/154742504910672534362390528), (-1768855004495/154742504910672534362390528)), (6901/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775746443078971/4835703278458516698824704), (-414524235129/2417851639229258349412352)), (12941/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260485309769729/604462909807314587353088), (-1450630218813/604462909807314587353088)), (11325/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236318538600657/9444732965739290427392), (-2356890519687/75557863725914323419136)), (9203/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324901497880513/1180591620717411303424), (-1767332298993/4722366482869645213696)), (55229/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406072133135331/147573952589676412928), (-1214768332003/295147905179352825856)), (18989/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1827023532339163/73786976294838206464), (-379512889145/9223372036854775808)), (94971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456661799326909/2305843009213693952), (-3414491891593/9223372036854775808)), (53439/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199736614834015/144115188075855872), (-3413087128137/1152921504606846976)), (53461/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197996307599103/144115188075855872), (-2984871393775/144115188075855872)), (11701/18014398509481984), by norm_num⟩
  | 4 => ⟨((374188615490475/9007199254740992), (-4474148692845/36028797018963968)), (140511/36028797018963968), by norm_num⟩
  | 3 => ⟨((747821534494221/4503599627370496), (-1396790392473/2251799813685248)), (175813/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120343046701777/2251799813685248), (-5578880925803/2251799813685248)), (44019/562949953421312), by norm_num⟩
  | 1 => ⟨((139695563003117/140737488355328), (-8347640079557/1125899906842624)), (66193/281474976710656), by norm_num⟩
  | 0 => ⟨((2218457549936615/2251799813685248), (-33225353466001/2251799813685248)), (1064359/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218457549936615/2251799813685248), (-33225353466001/2251799813685248)), (4060207375533293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2185118742285143/2251799813685248), (-32733387665279/1125899906842624)), (2128609/2251799813685248), by norm_num⟩
  | 2 => ⟨((2118508932375473/2251799813685248), (-127056301277205/2251799813685248)), (4254923/2251799813685248), by norm_num⟩
  | 3 => ⟨((248242359605101/281474976710656), (-119535452278873/1125899906842624)), (8486285/2251799813685248), by norm_num⟩
  | 4 => ⟨((1726085197058711/2251799813685248), (-421689531011827/2251799813685248)), (8385323/1125899906842624), by norm_num⟩
  | 5 => ⟨((1244137258522675/2251799813685248), (-323240126769051/1125899906842624)), (31991805/2251799813685248), by norm_num⟩
  | 6 => ⟨((62724314621711/281474976710656), (-357185468014415/1125899906842624)), (26860411/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-875474845/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-69045391/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((86198216698453/4503599627370496), (-679801251560643/2251799813685248)), (211941421/4503599627370496), by norm_num⟩
  | 1 => ⟨((-113960363/4294967296), (1797494205/4294967296)), (141/2147483648), by norm_num⟩
  | 2 => ⟨((9873913/536870912), (-155741005/536870912)), (99/2147483648), by norm_num⟩
  | 3 => ⟨((-36501733/4294967296), (1151482011/8589934592)), (185/8589934592), by norm_num⟩
  | 4 => ⟨((101204293/34359738368), (-1596293019/34359738368)), (129/17179869184), by norm_num⟩
  | 5 => ⟨((-112239153/137438953472), (1770345609/137438953472)), (9/4294967296), by norm_num⟩
  | 6 => ⟨((103731003/549755813888), (-1636146757/549755813888)), (67/137438953472), by norm_num⟩
  | 7 => ⟨((-82172403/2199023255552), (648051721/1099511627776)), (107/1099511627776), by norm_num⟩
  | 8 => ⟨((113915139/17592186044416), (-1796780893/17592186044416)), (299/17592186044416), by norm_num⟩
  | 9 => ⟨((-70186629/70368744177664), (553526049/35184372088832)), (93/35184372088832), by norm_num⟩
  | 10 => ⟨((38919731/281474976710656), (-1227760065/562949953421312)), (13/35184372088832), by norm_num⟩
  | 11 => ⟨((-39239421/2251799813685248), (1237844985/4503599627370496)), (53/1125899906842624), by norm_num⟩
  | 12 => ⟨((72529851/36028797018963968), (-572005841/18014398509481984)), (99/18014398509481984), by norm_num⟩
  | 13 => ⟨((-30937761/144115188075855872), (1951922393/576460752303423488)), (85/144115188075855872), by norm_num⟩
  | 14 => ⟨((98031643/4611686018427387904), (-1546250861/4611686018427387904)), (271/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-72480381/36893488147419103232), (571615693/18446744073709551616)), (101/18446744073709551616), by norm_num⟩
  | 16 => ⟨((100479143/590295810358705651712), (-198106903/73786976294838206464)), (141/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-981831479579/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780122128329463/633825300114114700748351602688), (-581816000401/158456325028528675187087900672)), (92429/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891264039237839/39614081257132168796771975168), (-1308944583919/19807040628566084398385987584)), (103997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236391729495953/309485009821345068724781056), (-1390583685335/1237940039285380274899124224)), (55257/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772799620497771/154742504910672534362390528), (-1390392519651/77371252455336267181195264)), (110533/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387765326561345/2417851639229258349412352), (-1303289891249/4835703278458516698824704)), (103645/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260107585599865/604462909807314587353088), (-1140175578727/302231454903657293676544)), (45355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889934335133083/75557863725914323419136), (-926202294909/18889465931478580854784)), (147441/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299145360987057/4722366482869645213696), (-2777940699141/4722366482869645213696)), (110615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811827460794851/295147905179352825856), (-954646516937/147573952589676412928)), (152149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826231153121149/73786976294838206464), (-2385804635479/36893488147419103232)), (47567/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825755268768705/9223372036854775808), (-1341457205801/2305843009213693952)), (107081/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798500181879385/576460752303423488), (-2681519994971/576460752303423488)), (107151/576460752303423488), by norm_num⟩
  | 5 => ⟨((74825913674101/9007199254740992), (-4689523482573/144115188075855872)), (23459/18014398509481984), by norm_num⟩
  | 4 => ⟨((373895131431861/9007199254740992), (-878501816313/4503599627370496)), (281823/36028797018963968), by norm_num⟩
  | 3 => ⟨((93385825082493/562949953421312), (-8774049683795/9007199254740992)), (176415/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118869523748913/2251799813685248), (-8757607445997/2251799813685248)), (353659/2251799813685248), by norm_num⟩
  | 1 => ⟨((557672568260753/562949953421312), (-13095342317625/1125899906842624)), (266281/562949953421312), by norm_num⟩
  | 0 => ⟨((1104754037768443/1125899906842624), (-13013315079001/562949953421312)), (1073437/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104754037768443/1125899906842624), (-13013315079001/562949953421312)), (4094837193015670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((16928182445923/17592186044416), (-25537816089879/562949953421312)), (1078091/562949953421312), by norm_num⟩
  | 2 => ⟨((260048606234479/281474976710656), (-49147821532631/562949953421312)), (4345225/1125899906842624), by norm_num⟩
  | 3 => ⟨((952431385515869/1125899906842624), (-181626411532273/1125899906842624)), (4393815/562949953421312), by norm_num⟩
  | 4 => ⟨((1552779932633519/2251799813685248), (-307286098401175/1125899906842624)), (17702605/1125899906842624), by norm_num⟩
  | 5 => ⟨((28219461963115/70368744177664), (-105948069689575/281474976710656)), (68154867/2251799813685248), by norm_num⟩
  | 6 => ⟨((86198216698453/4503599627370496), (-679801251560643/2251799813685248)), (211941421/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-69045391/2097152)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-641273733/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((486578624217517/2251799813685248), (-562089348782123/4503599627370496)), (106652747/4503599627370496), by norm_num⟩
  | 1 => ⟨((-746839605/2147483648), (215684869/1073741824)), (21/536870912), by norm_num⟩
  | 2 => ⟨((1201991975/4294967296), (-694262811/4294967296)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((-1289687637/8589934592), (186228815/2147483648)), (149/8589934592), by norm_num⟩
  | 4 => ⟨((1037836089/17179869184), (-599447431/17179869184)), (61/8589934592), by norm_num⟩
  | 5 => ⟨((-1336266199/68719476736), (385909369/34359738368)), (159/68719476736), by norm_num⟩
  | 6 => ⟨((716879161/137438953472), (-103516195/34359738368)), (87/137438953472), by norm_num⟩
  | 7 => ⟨((-1318597143/1099511627776), (380806603/549755813888)), (81/549755813888), by norm_num⟩
  | 8 => ⟨((1061100117/4398046511104), (-76610573/549755813888)), (33/1099511627776), by norm_num⟩
  | 9 => ⟨((-759011003/17592186044416), (109599965/4398046511104)), (3/549755813888), by norm_num⟩
  | 10 => ⟨((244316217/35184372088832), (-141115471/35184372088832)), (63/70368744177664), by norm_num⟩
  | 11 => ⟨((-1143888821/1125899906842624), (660702805/1125899906842624)), (75/562949953421312), by norm_num⟩
  | 12 => ⟨((613672679/4503599627370496), (-354453381/4503599627370496)), (163/9007199254740992), by norm_num⟩
  | 13 => ⟨((-607795739/36028797018963968), (702117797/72057594037927936)), (41/18014398509481984), by norm_num⟩
  | 14 => ⟨((1117953721/576460752303423488), (-322861429/288230376151711744)), (153/576460752303423488), by norm_num⟩
  | 15 => ⟨((-959614455/4611686018427387904), (554267119/4611686018427387904)), (133/4611686018427387904), by norm_num⟩
  | 16 => ⟨((772219943/36893488147419103232), (-223014629/18446744073709551616)), (109/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-341141757273/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827593694475/633825300114114700748351602688), (-101045232341/79228162514264337593543950336)), (11535/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945466438133575/19807040628566084398385987584), (-454647530281/19807040628566084398385987584)), (25955/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945391104844385/1237940039285380274899124224), (-241497288235/618970019642690137449562112)), (110315/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27694504028149/2417851639229258349412352), (-120729403923/19342813113834066795298816)), (110321/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550732183682657/9671406556917033397649408), (-905307020867/9671406556917033397649408)), (103433/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259819883219521/604462909807314587353088), (-24749380373/18889465931478580854784)), (90511/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889467343287615/75557863725914323419136), (-643330674883/37778931862957161709568)), (147093/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81174723490097/295147905179352825856), (-241181991369/1180591620717411303424)), (27583/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405793678013743/147573952589676412928), (-1326065524621/590295810358705651712)), (151725/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825632008046219/73786976294838206464), (-1656929023207/73786976294838206464)), (47421/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456270691263629/2305843009213693952), (-1863147858743/9223372036854775808)), (106717/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99770611026081/72057594037927936), (-1862026874723/1152921504606846976)), (106741/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196630008381533/144115188075855872), (-203501659509/18014398509481984)), (46713/36028797018963968), by norm_num⟩
  | 4 => ⟨((747353955582951/18014398509481984), (-1219750801613/18014398509481984)), (70097/9007199254740992), by norm_num⟩
  | 3 => ⟨((746544973234519/4503599627370496), (-1522487416585/4503599627370496)), (350677/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235595023998741/4503599627370496), (-3038381312669/2251799813685248)), (701931/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227530265080891/2251799813685248), (-4541122195515/1125899906842624)), (1054345/2251799813685248), by norm_num⟩
  | 0 => ⟨((550852760373725/562949953421312), (-9016649084013/1125899906842624)), (1057253/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550852760373725/562949953421312), (-9016649084013/1125899906842624)), (4033100132468795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2155917674579487/2251799813685248), (-35291563714067/2251799813685248)), (1043001/562949953421312), by norm_num⟩
  | 2 => ⟨((2063565107721583/2251799813685248), (-33788841047191/1125899906842624)), (8119491/2251799813685248), by norm_num⟩
  | 3 => ⟨((944518732268471/1125899906842624), (-123857321581749/2251799813685248)), (7684429/1125899906842624), by norm_num⟩
  | 4 => ⟨((1577903099876267/2251799813685248), (-51952025065277/562949953421312)), (27476595/2251799813685248), by norm_num⟩
  | 5 => ⟨((543252995047761/1125899906842624), (-291234632482507/2251799813685248)), (43578709/2251799813685248), by norm_num⟩
  | 6 => ⟨((486578624217517/2251799813685248), (-562089348782123/4503599627370496)), (106652747/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-641273733/16777216)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1427837973/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((67660496137147/2251799813685248), (1901423932529455/9007199254740992)), (9147517/562949953421312), by norm_num⟩
  | 1 => ⟨((-57807605/1073741824), (-812266907/2147483648)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((207154647/4294967296), (727693461/2147483648)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((-123723767/4294967296), (-869234433/4294967296)), (141/8589934592), by norm_num⟩
  | 4 => ⟨((221683231/17179869184), (1557459027/17179869184)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-158881211/34359738368), (-69764799/2147483648)), (93/34359738368), by norm_num⟩
  | 6 => ⟨((94892305/68719476736), (1333351885/137438953472)), (113/137438953472), by norm_num⟩
  | 7 => ⟨((-48578339/137438953472), (-682584533/274877906944)), (59/274877906944), by norm_num⟩
  | 8 => ⟨((87040699/1099511627776), (1223027301/2199023255552)), (107/2199023255552), by norm_num⟩
  | 9 => ⟨((-138627553/8796093022208), (-973942555/8796093022208)), (87/8796093022208), by norm_num⟩
  | 10 => ⟨((198709785/70368744177664), (1396056637/70368744177664)), (127/70368744177664), by norm_num⟩
  | 11 => ⟨((-258938283/562949953421312), (-1819198327/562949953421312)), (167/562949953421312), by norm_num⟩
  | 12 => ⟨((154651707/2251799813685248), (1086521943/2251799813685248)), (101/2251799813685248), by norm_num⟩
  | 13 => ⟨((-170522253/18014398509481984), (-599011071/9007199254740992)), (113/18014398509481984), by norm_num⟩
  | 14 => ⟨((174591349/144115188075855872), (613305005/72057594037927936)), (117/144115188075855872), by norm_num⟩
  | 15 => ⟨((-166840375/1152921504606846976), (-36629835/36028797018963968)), (57/576460752303423488), by norm_num⟩
  | 16 => ⟨((149468911/9223372036854775808), (262527415/2305843009213693952)), (13/1152921504606846976), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (465491387071/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889791342188443/316912650057057350374175801344), (275683004317/79228162514264337593543950336)), (46209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472664314603365/9903520314283042199192993792), (620201219943/9903520314283042199192993792)), (6499/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890489243380961/2475880078570760549798248448), (658859801115/618970019642690137449562112)), (27625/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443038788489243/38685626227668133590597632), (1317485650557/77371252455336267181195264)), (55259/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550457252779271/9671406556917033397649408), (617447132949/2417851639229258349412352)), (51815/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78723698295257/37778931862957161709568), (135035499821/37778931862957161709568)), (45347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889075915267055/75557863725914323419136), (3509991381463/75557863725914323419136)), (18427/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298501765743713/4722366482869645213696), (2631678575399/4722366482869645213696)), (55297/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622770335036145/590295810358705651712), (1808617053863/295147905179352825856)), (38029/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912562977613221/36893488147419103232), (2259778697687/36893488147419103232)), (95111/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824512657070139/9223372036854775808), (5081773439605/9223372036854775808)), (107053/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595758671824879/1152921504606846976), (1269591065599/288230376151711744)), (6695/72057594037927936), by norm_num⟩
  | 5 => ⟨((299032293217397/36028797018963968), (4439735619373/144115188075855872)), (93805/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493954425380575/36028797018963968), (1662985685733/9007199254740992)), (17607/4503599627370496), by norm_num⟩
  | 3 => ⟨((1492144194621259/9007199254740992), (8301534677339/9007199254740992)), (176331/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233691885524255/4503599627370496), (16562937884127/4503599627370496)), (353449/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224646641769621/2251799813685248), (773257885243/70368744177664)), (33259/140737488355328), by norm_num⟩
  | 0 => ⟨((1098764578701663/1125899906842624), (3068058200891/140737488355328)), (536095/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098764578701663/1125899906842624), (3068058200891/140737488355328)), (2045040134910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2143496346849189/2251799813685248), (47905838251469/1125899906842624)), (1069723/1125899906842624), by norm_num⟩
  | 2 => ⟨((3977197661141/4398046511104), (182406959376585/2251799813685248)), (1063789/562949953421312), by norm_num⟩
  | 3 => ⟨((1826693477158127/2251799813685248), (329904893173259/2251799813685248)), (8385339/2251799813685248), by norm_num⟩
  | 4 => ⟨((716753727692507/1125899906842624), (267623752688691/1125899906842624)), (8030825/1125899906842624), by norm_num⟩
  | 5 => ⟨((785351220780809/2251799813685248), (681482683115593/2251799813685248)), (28085493/2251799813685248), by norm_num⟩
  | 6 => ⟨((67660496137147/2251799813685248), (1901423932529455/9007199254740992)), (9147517/562949953421312), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1427837973/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-775339673/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-515972581927147/4503599627370496), (-663791623995495/4503599627370496)), (151309575/4503599627370496), by norm_num⟩
  | 1 => ⟨((29922613/134217728), (153980119/536870912)), (71/1073741824), by norm_num⟩
  | 2 => ⟨((-931627461/4294967296), (-1198525905/4294967296)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((604287777/4294967296), (194351977/1073741824)), (91/2147483648), by norm_num⟩
  | 4 => ⟨((-587944859/8589934592), (-756382969/8589934592)), (179/8589934592), by norm_num⟩
  | 5 => ⟨((915270295/34359738368), (1177482637/34359738368)), (281/34359738368), by norm_num⟩
  | 6 => ⟨((-593677919/68719476736), (-763758471/68719476736)), (23/8589934592), by norm_num⟩
  | 7 => ⟨((660139365/274877906944), (424630103/137438953472)), (103/137438953472), by norm_num⟩
  | 8 => ⟨((-642285945/1099511627776), (-826292027/1099511627776)), (101/549755813888), by norm_num⟩
  | 9 => ⟨((69435041/549755813888), (178654449/1099511627776)), (177/4398046511104), by norm_num⟩
  | 10 => ⟨((-432365923/17592186044416), (-556232809/17592186044416)), (139/17592186044416), by norm_num⟩
  | 11 => ⟨((305943723/70368744177664), (787184777/140737488355328)), (99/70368744177664), by norm_num⟩
  | 12 => ⟨((-49611583/70368744177664), (-510596949/562949953421312)), (259/1125899906842624), by norm_num⟩
  | 13 => ⟨((475272285/4503599627370496), (152857813/1125899906842624)), (157/4503599627370496), by norm_num⟩
  | 14 => ⟨((-528478379/36028797018963968), (-679880159/36028797018963968)), (11/2251799813685248), by norm_num⟩
  | 15 => ⟨((548464769/288230376151711744), (352796187/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 16 => ⟨((-133407895/576460752303423488), (-686509681/2305843009213693952)), (45/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-1453420628113/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889686916232375/316912650057057350374175801344), (-1721172650425/316912650057057350374175801344)), (92539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945211059353503/19807040628566084398385987584), (-1936026270897/19807040628566084398385987584)), (1627/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((945119586440417/1237940039285380274899124224), (-128542183129/77371252455336267181195264)), (110661/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442976204938081/38685626227668133590597632), (-4112555687023/154742504910672534362390528)), (110689/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550222284443319/9671406556917033397649408), (-1927338619003/4835703278458516698824704)), (103801/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629686647799403/302231454903657293676544), (-1685999483091/302231454903657293676544)), (90857/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472185210163371/18889465931478580854784), (-5477916753865/75557863725914323419136)), (73849/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81140625089555/295147905179352825856), (-4107053910973/4722366482869645213696)), (110823/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622423415036127/590295810358705651712), (-5644951094435/590295810358705651712)), (76231/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228086398803053/9223372036854775808), (-3526408764105/36893488147419103232)), (190697/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824022015937687/9223372036854775808), (-7929785281745/9223372036854775808)), (53675/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398816530115353/288230376151711744), (-7923993969147/1152921504606846976)), (53727/288230376151711744), by norm_num⟩
  | 5 => ⟨((597848022894031/72057594037927936), (-6926981884345/144115188075855872)), (94139/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493300456399431/36028797018963968), (-10377453129415/36028797018963968)), (70721/9007199254740992), by norm_num⟩
  | 3 => ⟨((186414908850511/1125899906842624), (-6474522712619/4503599627370496)), (44303/1125899906842624), by norm_num⟩
  | 2 => ⟨((279002468515503/562949953421312), (-12914915981819/2251799813685248)), (177827/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111041526817165/1125899906842624), (-9643572651727/562949953421312)), (536561/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096091251065101/1125899906842624), (-19116974024759/562949953421312)), (1085481/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096091251065101/1125899906842624), (-19116974024759/562949953421312)), (4140781406882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065773421407461/1125899906842624), (-18610844399249/281474976710656)), (2187209/1125899906842624), by norm_num⟩
  | 2 => ⟨((1003935751696009/1125899906842624), (-550530268891/4398046511104)), (1107511/281474976710656), by norm_num⟩
  | 3 => ⟨((438770845538201/562949953421312), (-125668752691693/562949953421312)), (9009383/1125899906842624), by norm_num⟩
  | 4 => ⟨((1255722420205685/2251799813685248), (-391791735952049/1125899906842624)), (18066447/1125899906842624), by norm_num⟩
  | 5 => ⟨((106896240655401/562949953421312), (-873934998833003/2251799813685248)), (32723169/1125899906842624), by norm_num⟩
  | 6 => ⟨((-515972581927147/4503599627370496), (-663791623995495/4503599627370496)), (151309575/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-775339673/16777216)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-207136173/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((954382468600267/9007199254740992), (577676712357185/4503599627370496)), (179199901/9007199254740992), by norm_num⟩
  | 1 => ⟨((-59145169/268435456), (-286399115/1073741824)), (181/4294967296), by norm_num⟩
  | 2 => ⟨((245977843/1073741824), (595550217/2147483648)), (3/67108864), by norm_num⟩
  | 3 => ⟨((-681995393/4294967296), (-206401977/1073741824)), (17/536870912), by norm_num⟩
  | 4 => ⟨((88635597/1073741824), (858401691/8589934592)), (9/536870912), by norm_num⟩
  | 5 => ⟨((-73725017/2147483648), (-356999227/8589934592)), (61/8589934592), by norm_num⟩
  | 6 => ⟨((817636603/68719476736), (989812031/68719476736)), (43/17179869184), by norm_num⟩
  | 7 => ⟨((-485779291/137438953472), (-2297161/536870912)), (13/17179869184), by norm_num⟩
  | 8 => ⟨((505074819/549755813888), (611431937/549755813888)), (55/274877906944), by norm_num⟩
  | 9 => ⟨((-466788249/2199023255552), (-1130166195/4398046511104)), (103/2199023255552), by norm_num⟩
  | 10 => ⟨((776527101/17592186044416), (470022907/8796093022208)), (173/17592186044416), by norm_num⟩
  | 11 => ⟨((-18349349/2199023255552), (-355412785/35184372088832)), (133/70368744177664), by norm_num⟩
  | 12 => ⟨((407001585/281474976710656), (985413479/562949953421312)), (187/562949953421312), by norm_num⟩
  | 13 => ⟨((-130205539/562949953421312), (-157623825/562949953421312)), (61/1125899906842624), by norm_num⟩
  | 14 => ⟨((309434065/9007199254740992), (93648437/2251799813685248)), (147/18014398509481984), by norm_num⟩
  | 15 => ⟨((-686346719/144115188075855872), (-830875521/144115188075855872)), (165/144115188075855872), by norm_num⟩
  | 16 => ⟨((178402235/288230376151711744), (863878537/1152921504606846976)), (87/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (573390376603/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444800384437253/158456325028528675187087900672), (1357785011021/633825300114114700748351602688)), (46167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890228625980753/39614081257132168796771975168), (763633386415/19807040628566084398385987584)), (103885/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890034018241385/2475880078570760549798248448), (1622423994087/2475880078570760549798248448)), (110387/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771700150150941/154742504910672534362390528), (1622090016435/154742504910672534362390528)), (55199/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550030921793395/9671406556917033397649408), (760177314369/4835703278458516698824704)), (51755/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259206368098569/604462909807314587353088), (664977819631/302231454903657293676544)), (90583/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944235274074583/37778931862957161709568), (1080256569373/37778931862957161709568)), (36805/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649024062775985/2361183241434822606848), (809901694959/2361183241434822606848)), (55217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811073602628513/295147905179352825856), (556571295765/147573952589676412928)), (151879/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912173990283357/36893488147419103232), (1390720231709/36893488147419103232)), (23737/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227954840456563/1152921504606846976), (195448414991/576460752303423488)), (213699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594886346887191/1152921504606846976), (3124743996527/1152921504606846976)), (213781/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597683847936239/72057594037927936), (1365709435399/72057594037927936)), (93575/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492815818995165/36028797018963968), (4091669917891/36028797018963968)), (140455/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490727240138941/9007199254740992), (2552524199153/4503599627370496)), (351461/9007199254740992), by norm_num⟩
  | 2 => ⟨((139429802334493/281474976710656), (5090766226787/2251799813685248)), (351947/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220471047825961/2251799813685248), (3800267951889/562949953421312)), (132285/281474976710656), by norm_num⟩
  | 0 => ⟨((68417651350707/70368744177664), (15059168799301/1125899906842624)), (2126347/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((68417651350707/70368744177664), (15059168799301/1125899906842624)), (8111370095259856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((133016134287165/140737488355328), (58566511173809/2251799813685248)), (4191663/2251799813685248), by norm_num⟩
  | 2 => ⟨((502492793022881/562949953421312), (55353346191297/1125899906842624)), (2035357/562949953421312), by norm_num⟩
  | 3 => ⟨((1788670607583445/2251799813685248), (197635028561843/2251799813685248)), (15334709/2251799813685248), by norm_num⟩
  | 4 => ⟨((87715472050173/140737488355328), (156987297214021/1125899906842624)), (27053399/2251799813685248), by norm_num⟩
  | 5 => ⟨((830928653670881/2251799813685248), (391373046142253/2251799813685248)), (20633321/1125899906842624), by norm_num⟩
  | 6 => ⟨((954382468600267/9007199254740992), (577676712357185/4503599627370496)), (179199901/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-207136173/4194304)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile027Terms0

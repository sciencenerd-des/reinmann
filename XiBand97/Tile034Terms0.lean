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
namespace Reinmann.XiBand97.Tile034Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32547/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32547/1280))
  have he : value ((69/80), (32547/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1182786455/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((26260704159403/140737488355328), (582517346350585/1125899906842624)), (85946825/2251799813685248), by norm_num⟩
  | 1 => ⟨((-69437153/536870912), (-1540261293/4294967296)), (29/1073741824), by norm_num⟩
  | 2 => ⟨((385041335/8589934592), (1067627773/8589934592)), (83/8589934592), by norm_num⟩
  | 3 => ⟨((-177926877/17179869184), (-493348787/17179869184)), (79/34359738368), by norm_num⟩
  | 4 => ⟨((493318053/274877906944), (1367853283/274877906944)), (7/17179869184), by norm_num⟩
  | 5 => ⟨((-136776807/549755813888), (-1516997835/2199023255552)), (127/2199023255552), by norm_num⟩
  | 6 => ⟨((505634443/17592186044416), (87625231/1099511627776)), (15/2199023255552), by norm_num⟩
  | 7 => ⟨((-200273765/70368744177664), (-1110622753/140737488355328)), (97/140737488355328), by norm_num⟩
  | 8 => ⟨((277638391/1125899906842624), (384912515/562949953421312)), (137/2251799813685248), by norm_num⟩
  | 9 => ⟨((-342123143/18014398509481984), (-948625865/18014398509481984)), (43/9007199254740992), by norm_num⟩
  | 10 => ⟨((379426707/288230376151711744), (526029875/144115188075855872)), (97/288230376151711744), by norm_num⟩
  | 11 => ⟨((-382543349/4611686018427387904), (-530350727/2305843009213693952)), (25/1152921504606846976), by norm_num⟩
  | 12 => ⟨((353545125/73786976294838206464), (122537037/9223372036854775808)), (47/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-301610839/1180591620717411303424), (-836294909/1180591620717411303424)), (41/590295810358705651712), by norm_num⟩
  | 14 => ⟨((477853035/37778931862957161709568), (331243119/9444732965739290427392)), (33/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-353303983/604462909807314587353088), (-979627665/604462909807314587353088)), (99/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((489783319/19342813113834066795298816), (339513077/4835703278458516698824704)), (139/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (1595261982213/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781046516035879/633825300114114700748351602688), (1892510887983/633825300114114700748351602688)), (23097/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236537993333255/4951760157141521099596496896), (2128957678755/39614081257132168796771975168)), (51973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892238708728043/2475880078570760549798248448), (565469801995/618970019642690137449562112)), (55229/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773904460714371/154742504910672534362390528), (2261723582681/154742504910672534362390528)), (13809/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776048529662631/4835703278458516698824704), (1060100250473/4835703278458516698824704)), (51793/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315253458717637/151115727451828646838272), (927505036917/302231454903657293676544)), (45327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891406925075391/75557863725914323419136), (3014081297381/75557863725914323419136)), (73671/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300249746353211/4722366482869645213696), (1130144822677/2361183241434822606848)), (55267/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101573334905809/36893488147419103232), (3107457328369/590295810358705651712)), (38007/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228516132429037/9223372036854775808), (485457526643/9223372036854775808)), (47525/36893488147419103232), by norm_num⟩
  | 7 => ⟨((57121569391955/288230376151711744), (2184104087285/4611686018427387904)), (3343/288230376151711744), by norm_num⟩
  | 6 => ⟨((199891884204475/144115188075855872), (8529435753/2251799813685248)), (53517/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199082216607187/144115188075855872), (1909953930167/72057594037927936)), (46859/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498381372854565/36028797018963968), (715912836461/4503599627370496)), (140705/36028797018963968), by norm_num⟩
  | 3 => ⟨((46802290367553/281474976710656), (1788662269715/2251799813685248)), (22013/1125899906842624), by norm_num⟩
  | 2 => ⟨((561184074099747/1125899906842624), (7147928431961/2251799813685248)), (176439/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120589361815915/1125899906842624), (10705085049937/1125899906842624)), (265499/1125899906842624), by norm_num⟩
  | 0 => ⟨((557613682659859/562949953421312), (21342904088703/1125899906842624)), (534361/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557613682659859/562949953421312), (21342904088703/1125899906842624)), (2038425449851607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1104251407471519/1125899906842624), (21140592116989/562949953421312)), (269713/281474976710656), by norm_num⟩
  | 2 => ⟨((135178920542001/140737488355328), (41468213041125/562949953421312)), (1098623/562949953421312), by norm_num⟩
  | 3 => ⟨((4033632264999/4398046511104), (2489399031671/17592186044416)), (4544637/1125899906842624), by norm_num⟩
  | 4 => ⟨((924504712926031/1125899906842624), (146120441125901/562949953421312)), (2405585/281474976710656), by norm_num⟩
  | 5 => ⟨((341639708062727/562949953421312), (119983166935823/281474976710656)), (2599685/140737488355328), by norm_num⟩
  | 6 => ⟨((26260704159403/140737488355328), (582517346350585/1125899906842624)), (85946825/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1182786455/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1874672179/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-823155273245127/2251799813685248), (-290755855721345/2251799813685248)), (226007353/4503599627370496), by norm_num⟩
  | 1 => ⟨((862434863/2147483648), (152315119/1073741824)), (15/268435456), by norm_num⟩
  | 2 => ⟨((-947481539/4294967296), (-334670523/4294967296)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((1387886483/17179869184), (245115433/8589934592)), (199/17179869184), by norm_num⟩
  | 4 => ⟨((-762374573/34359738368), (-269286827/34359738368)), (221/68719476736), by norm_num⟩
  | 5 => ⟨((1340086519/274877906944), (118336727/68719476736)), (197/274877906944), by norm_num⟩
  | 6 => ⟨((-981490345/1099511627776), (-346683153/1099511627776)), (147/1099511627776), by norm_num⟩
  | 7 => ⟨((1232316977/8796093022208), (435280425/8796093022208)), (187/8796093022208), by norm_num⟩
  | 8 => ⟨((-1353838575/70368744177664), (-59775553/8796093022208)), (13/4398046511104), by norm_num⟩
  | 9 => ⟨((1322083285/562949953421312), (58373473/70368744177664)), (205/562949953421312), by norm_num⟩
  | 10 => ⟨((-1161965555/4503599627370496), (-410430815/4503599627370496)), (183/4503599627370496), by norm_num⟩
  | 11 => ⟨((928399737/36028797018963968), (327930427/36028797018963968)), (37/9007199254740992), by norm_num⟩
  | 12 => ⟨((-1359935147/576460752303423488), (-480357863/576460752303423488)), (219/576460752303423488), by norm_num⟩
  | 13 => ⟨((229852533/1152921504606846976), (324755109/4611686018427387904)), (75/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-1154371737/73786976294838206464), (-203874259/36893488147419103232)), (191/73786976294838206464), by norm_num⟩
  | 15 => ⟨((338188527/295147905179352825856), (59727671/147573952589676412928)), (113/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-1486152287/18889465931478580854784), (-524940427/18889465931478580854784)), (251/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-228124025213/633825300114114700748351602688)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780498168628739/633825300114114700748351602688), (-4327601490707/633825300114114700748351602688)), (69469/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891686617402793/39614081257132168796771975168), (-2434055768045/19807040628566084398385987584)), (78173/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236447781338449/309485009821345068724781056), (-5171865005623/2475880078570760549798248448)), (83083/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886623694483035/77371252455336267181195264), (-323206146387/9671406556917033397649408)), (83109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387870100673771/2417851639229258349412352), (-2423744975727/4835703278458516698824704)), (77943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260473608699935/604462909807314587353088), (-1060237819569/151115727451828646838272)), (68229/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472631959071741/18889465931478580854784), (-1722603969943/18889465931478580854784)), (110925/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649794680841643/2361183241434822606848), (-2583411406795/2361183241434822606848)), (10405/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624263594928509/590295810358705651712), (-7102773352591/590295810358705651712)), (114531/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913494627367501/36893488147419103232), (-2219013345587/18446744073709551616)), (143277/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826604367726631/9223372036854775808), (-9982239671995/9223372036854775808)), (161343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597844759358253/1152921504606846976), (-2494521517945/288230376151711744)), (80769/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197948178250901/144115188075855872), (-8726148228745/144115188075855872)), (141565/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496670303051897/36028797018963968), (-6539928744625/18014398509481984)), (53197/9007199254740992), by norm_num⟩
  | 3 => ⟨((373879241397093/2251799813685248), (-4083352347463/2251799813685248)), (266755/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120185653788555/2251799813685248), (-254824107673/35184372088832)), (33489/281474976710656), by norm_num⟩
  | 1 => ⟨((1117250427798063/1125899906842624), (-12200640778405/562949953421312)), (404765/1125899906842624), by norm_num⟩
  | 0 => ⟨((277072524593227/281474976710656), (-24277119343613/562949953421312)), (410575/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277072524593227/281474976710656), (-24277119343613/562949953421312)), (1566219331981468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((136107728205485/140737488355328), (-2987176171481/35184372088832)), (843719/562949953421312), by norm_num⟩
  | 2 => ⟨((1044926542225923/1125899906842624), (-92445080201705/562949953421312)), (3550385/1125899906842624), by norm_num⟩
  | 3 => ⟨((939414863440491/1125899906842624), (-21449135356947/70368744177664)), (1939037/281474976710656), by norm_num⟩
  | 4 => ⟨((339605473217383/562949953421312), (-572687115500883/1125899906842624)), (4417819/281474976710656), by norm_num⟩
  | 5 => ⟨((236889579056923/2251799813685248), (-172739759265617/281474976710656)), (39297697/1125899906842624), by norm_num⟩
  | 6 => ⟨((-823155273245127/2251799813685248), (-290755855721345/2251799813685248)), (226007353/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1874672179/67108864)), (3/67108864), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1182786455/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-262181818913621/1125899906842624), (869551723794371/4503599627370496)), (244300341/4503599627370496), by norm_num⟩
  | 1 => ⟨((693247179/2147483648), (-287402785/1073741824)), (41/536870912), by norm_num⟩
  | 2 => ⟨((-961044655/4294967296), (99606215/536870912)), (115/2147483648), by norm_num⟩
  | 3 => ⟨((888193857/8589934592), (-184111379/2147483648)), (215/8589934592), by norm_num⟩
  | 4 => ⟨((-153912267/4294967296), (510465133/17179869184)), (151/17179869184), by norm_num⟩
  | 5 => ⟨((682776665/68719476736), (-141530987/17179869184)), (169/68719476736), by norm_num⟩
  | 6 => ⟨((-631019627/274877906944), (523209625/274877906944)), (79/137438953472), by norm_num⟩
  | 7 => ⟨((249936843/549755813888), (-207235015/549755813888)), (253/2199023255552), by norm_num⟩
  | 8 => ⟨((-86621509/1099511627776), (574577465/8796093022208)), (177/8796093022208), by norm_num⟩
  | 9 => ⟨((26685091/2199023255552), (-354014889/35184372088832)), (55/17592186044416), by norm_num⟩
  | 10 => ⟨((-473515407/281474976710656), (785230151/562949953421312)), (123/281474976710656), by norm_num⟩
  | 11 => ⟨((477404901/2251799813685248), (-791680095/4503599627370496)), (125/2251799813685248), by norm_num⟩
  | 12 => ⟨((-441215815/18014398509481984), (91458471/4503599627370496)), (233/36028797018963968), by norm_num⟩
  | 13 => ⟨((752806149/288230376151711744), (-312094431/144115188075855872)), (201/288230376151711744), by norm_num⟩
  | 14 => ⟨((-596349097/2305843009213693952), (494462571/2305843009213693952)), (161/2305843009213693952), by norm_num⟩
  | 15 => ⟨((440914875/18446744073709551616), (-731168719/36893488147419103232)), (15/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-611237805/295147905179352825856), (31675471/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1595261982213/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890058693824885/316912650057057350374175801344), (1890648172089/316912650057057350374175801344)), (23143/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472814606571785/9903520314283042199192993792), (4253487504363/39614081257132168796771975168)), (104167/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945563761217303/1237940039285380274899124224), (2259388447031/1237940039285380274899124224)), (110705/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772792913601133/154742504910672534362390528), (4518154015671/154742504910672534362390528)), (6921/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1551054600735083/9671406556917033397649408), (4235107534739/9671406556917033397649408)), (12981/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315025325164233/151115727451828646838272), (463132148179/75557863725914323419136)), (22725/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944961669714427/37778931862957161709568), (752434592309/9444732965739290427392)), (147775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649568214869559/2361183241434822606848), (1128380350843/1180591620717411303424)), (55443/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623641529550767/590295810358705651712), (6204326727313/590295810358705651712)), (152555/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456553186730261/18446744073709551616), (1938190060773/18446744073709551616)), (95413/36893488147419103232), by norm_num⟩
  | 7 => ⟨((114108267049903/576460752303423488), (8718213458007/9223372036854775808)), (214861/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596974509489107/1152921504606846976), (8713660311453/1152921504606846976)), (215089/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598594392380677/72057594037927936), (3809664641093/72057594037927936)), (188459/144115188075855872), by norm_num⟩
  | 4 => ⟨((747767680867593/18014398509481984), (1427342994821/4503599627370496)), (4425/562949953421312), by norm_num⟩
  | 3 => ⟨((1494105546426867/9007199254740992), (14255485842905/9007199254740992)), (177449/4503599627370496), by norm_num⟩
  | 2 => ⟨((139848139317223/281474976710656), (7114278234133/1125899906842624)), (178123/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115176796265675/1125899906842624), (10637732767613/562949953421312)), (537747/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104251407471519/1125899906842624), (21140592116989/562949953421312)), (1089031/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104251407471519/1125899906842624), (21140592116989/562949953421312)), (4154323582175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((135178920542001/140737488355328), (41468213041125/562949953421312)), (2217977/1125899906842624), by norm_num⟩
  | 2 => ⟨((4033632264999/4398046511104), (2489399031671/17592186044416)), (4587515/1125899906842624), by norm_num⟩
  | 3 => ⟨((924504712926031/1125899906842624), (146120441125901/562949953421312)), (4856563/562949953421312), by norm_num⟩
  | 4 => ⟨((341639708062727/562949953421312), (119983166935823/281474976710656)), (10496851/562949953421312), by norm_num⟩
  | 5 => ⟨((26260704159403/140737488355328), (582517346350585/1125899906842624)), (21689431/562949953421312), by norm_num⟩
  | 6 => ⟨((-262181818913621/1125899906842624), (869551723794371/4503599627370496)), (244300341/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1182786455/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1373172551/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1119952328324783/4503599627370496), (93200045471581/4503599627370496)), (183755193/4503599627370496), by norm_num⟩
  | 1 => ⟨((1718991983/4294967296), (-143050849/4294967296)), (71/1073741824), by norm_num⟩
  | 2 => ⟨((-1383305435/4294967296), (57557865/2147483648)), (115/2147483648), by norm_num⟩
  | 3 => ⟨((1484229475/8589934592), (-123514413/8589934592)), (249/8589934592), by norm_num⟩
  | 4 => ⟨((-597193797/8589934592), (49697195/8589934592)), (101/8589934592), by norm_num⟩
  | 5 => ⟨((1537834141/68719476736), (-7998455/4294967296)), (131/34359738368), by norm_num⟩
  | 6 => ⟨((-412508095/68719476736), (68656089/137438953472)), (283/274877906944), by norm_num⟩
  | 7 => ⟨((1517499811/1099511627776), (-31570775/274877906944)), (131/549755813888), by norm_num⟩
  | 8 => ⟨((-38161277/137438953472), (25405601/1099511627776)), (213/4398046511104), by norm_num⟩
  | 9 => ⟨((436751687/8796093022208), (-72691089/17592186044416)), (307/35184372088832), by norm_num⟩
  | 10 => ⟨((-562339779/70368744177664), (23398359/35184372088832)), (25/17592186044416), by norm_num⟩
  | 11 => ⟨((5142335/4398046511104), (-109551145/1125899906842624)), (59/281474976710656), by norm_num⟩
  | 12 => ⟨((-1412483227/9007199254740992), (29385961/2251799813685248)), (255/9007199254740992), by norm_num⟩
  | 13 => ⟨((1398956343/72057594037927936), (-58209083/36028797018963968)), (255/72057594037927936), by norm_num⟩
  | 14 => ⟨((-1286590501/576460752303423488), (13383415/72057594037927936)), (59/144115188075855872), by norm_num⟩
  | 15 => ⟨((1104366683/4611686018427387904), (-45951521/2305843009213693952)), (51/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-1777409609/73786976294838206464), (9244515/4611686018427387904)), (165/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (1992061912377/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779816042582419/633825300114114700748351602688), (4720345240237/633825300114114700748351602688)), (11583/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945459603148921/19807040628566084398385987584), (2654849851473/19807040628566084398385987584)), (104277/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890766833888027/2475880078570760549798248448), (2820376346867/1237940039285380274899124224)), (110829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886215962248337/77371252455336267181195264), (176245274943/4835703278458516698824704)), (110867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775357927148445/4835703278458516698824704), (660799717135/1208925819614629174706176)), (25995/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629902289292097/302231454903657293676544), (4624637371251/604462909807314587353088)), (5689/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1889440568502983/75557863725914323419136), (7513234220355/75557863725914323419136)), (147991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298773829135281/4722366482869645213696), (2816674527399/2361183241434822606848)), (111061/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25361595400867/9223372036854775808), (3871646206959/295147905179352825856)), (76409/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912793598221209/36893488147419103232), (4837635381273/36893488147419103232)), (47797/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825026783839687/9223372036854775808), (10879391530595/9223372036854775808)), (107657/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596266843318849/1152921504606846976), (1359097391659/144115188075855872)), (215599/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196567132485221/144115188075855872), (9506239644565/144115188075855872)), (188969/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494598007029571/36028797018963968), (14244467437937/36028797018963968)), (142047/18014398509481984), by norm_num⟩
  | 3 => ⟨((93307834223253/562949953421312), (17779505729319/9007199254740992)), (22265/562949953421312), by norm_num⟩
  | 2 => ⟨((558796106768477/1125899906842624), (17740353118907/2251799813685248)), (357927/2251799813685248), by norm_num⟩
  | 1 => ⟨((8698092856005/8796093022208), (26512527742235/1125899906842624)), (135279/281474976710656), by norm_num⟩
  | 0 => ⟨((1100484525877607/1125899906842624), (52632335213753/1125899906842624)), (1099183/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100484525877607/1125899906842624), (52632335213753/1125899906842624)), (4193050388816451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536591228777365/562949953421312), (51444244831645/562949953421312)), (2251509/1125899906842624), by norm_num⟩
  | 2 => ⟨((1013531077640921/1125899906842624), (6129437079613/35184372088832)), (4703677/1125899906842624), by norm_num⟩
  | 3 => ⟨((878207343697143/1125899906842624), (176566316231185/562949953421312)), (5053657/562949953421312), by norm_num⟩
  | 4 => ⟨((287123872417267/562949953421312), (1101780608534701/2251799813685248)), (44215441/2251799813685248), by norm_num⟩
  | 5 => ⟨((46683270781099/2251799813685248), (561946071678563/1125899906842624)), (88371045/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1119952328324783/4503599627370496), (93200045471581/4503599627370496)), (183755193/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1373172551/33554432)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1528729317/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-6328746154391/4503599627370496), (-240068344529367/1125899906842624)), (153478741/9007199254740992), by norm_num⟩
  | 1 => ⟨((10814277/4294967296), (410217981/1073741824)), (133/4294967296), by norm_num⟩
  | 2 => ⟨((-2422073/1073741824), (-45938247/134217728)), (121/4294967296), by norm_num⟩
  | 3 => ⟨((5786363/4294967296), (877976417/4294967296)), (73/4294967296), by norm_num⟩
  | 4 => ⟨((-10367771/17179869184), (-1573122559/17179869184)), (133/17179869184), by norm_num⟩
  | 5 => ⟨((7430621/34359738368), (1127462897/34359738368)), (97/34359738368), by norm_num⟩
  | 6 => ⟨((-2218981/34359738368), (-336690387/34359738368)), (59/68719476736), by norm_num⟩
  | 7 => ⟨((4543863/274877906944), (689449359/274877906944)), (61/274877906944), by norm_num⟩
  | 8 => ⟨((-4070755/1099511627776), (-617663709/1099511627776)), (111/2199023255552), by norm_num⟩
  | 9 => ⟨((3241695/4398046511104), (1967475199/17592186044416)), (179/17592186044416), by norm_num⟩
  | 10 => ⟨((-2323335/17592186044416), (-44065529/2199023255552)), (65/35184372088832), by norm_num⟩
  | 11 => ⟨((12110131/562949953421312), (1837494199/562949953421312)), (171/562949953421312), by norm_num⟩
  | 12 => ⟨((-3616407/1125899906842624), (-548724605/1125899906842624)), (13/281474976710656), by norm_num⟩
  | 13 => ⟨((3987527/9007199254740992), (605035389/9007199254740992)), (29/4503599627370496), by norm_num⟩
  | 14 => ⟨((-8165359/144115188075855872), (-1238946157/144115188075855872)), (15/18014398509481984), by norm_num⟩
  | 15 => ⟨((3901429/576460752303423488), (1183943205/1152921504606846976)), (29/288230376151711744), by norm_num⟩
  | 16 => ⟨((-13980845/18446744073709551616), (-2121341449/18446744073709551616)), (105/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-2054722421195/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111223882398759/39614081257132168796771975168), (-608445253603/158456325028528675187087900672)), (11555/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890656588854889/39614081257132168796771975168), (-1368812594407/19807040628566084398385987584)), (26003/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236311061285305/309485009821345068724781056), (-1454133807715/1237940039285380274899124224)), (55265/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772154353979323/154742504910672534362390528), (-2907751144725/154742504910672534362390528)), (55275/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550456453014801/9671406556917033397649408), (-2725468033137/9671406556917033397649408)), (51831/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259578423171375/604462909807314587353088), (-1192117979813/302231454903657293676544)), (22681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889074604002561/75557863725914323419136), (-1936677535069/37778931862957161709568)), (73733/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324625175191423/1180591620717411303424), (-2904116687197/4722366482869645213696)), (55317/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622768738311543/590295810358705651712), (-1995849475543/295147905179352825856)), (38045/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456280940234031/18446744073709551616), (-4987432115303/73786976294838206464)), (95155/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912254958007743/4611686018427387904), (-2803924400123/4611686018427387904)), (26777/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595755590623481/1152921504606846976), (-5604085014713/1152921504606846976)), (107181/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18689470230823/2251799813685248), (-1224835591351/36028797018963968)), (46933/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493949045690905/36028797018963968), (-7340555094047/36028797018963968)), (35241/9007199254740992), by norm_num⟩
  | 3 => ⟨((746068069516865/4503599627370496), (-9160904153115/9007199254740992)), (88247/4503599627370496), by norm_num⟩
  | 2 => ⟨((558417948827967/1125899906842624), (-4569372371695/1125899906842624)), (5529/70368744177664), by norm_num⟩
  | 1 => ⟨((556151651845563/562949953421312), (-13652806664623/1125899906842624)), (266479/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098704891402625/1125899906842624), (-27084900024323/1125899906842624)), (537317/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098704891402625/1125899906842624), (-27084900024323/1125899906842624)), (2049701694968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((535757592327147/562949953421312), (-26430690649337/562949953421312)), (2149059/2251799813685248), by norm_num⟩
  | 2 => ⟨((508637783141773/562949953421312), (-201232000816737/2251799813685248)), (4292303/2251799813685248), by norm_num⟩
  | 3 => ⟨((56883719857755/70368744177664), (-181817581066583/1125899906842624)), (4261773/1125899906842624), by norm_num⟩
  | 4 => ⟨((1412730037731999/2251799813685248), (-73487600691679/281474976710656)), (8266585/1125899906842624), by norm_num⟩
  | 5 => ⟨((183206650113221/562949953421312), (-184418064637963/562949953421312)), (14689037/1125899906842624), by norm_num⟩
  | 6 => ⟨((-6328746154391/4503599627370496), (-240068344529367/1125899906842624)), (153478741/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1528729317/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1660250689/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((148510881650121/1125899906842624), (74368099878573/562949953421312)), (5941951/281474976710656), by norm_num⟩
  | 1 => ⟨((-551202453/2147483648), (-69004841/268435456)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((67036903/268435456), (268554441/1073741824)), (177/4294967296), by norm_num⟩
  | 3 => ⟨((-347860773/2147483648), (-696777083/4294967296)), (29/1073741824), by norm_num⟩
  | 4 => ⟨((676905809/8589934592), (677932799/8589934592)), (115/8589934592), by norm_num⟩
  | 5 => ⟨((-1053758307/34359738368), (-1055357051/34359738368)), (181/34359738368), by norm_num⟩
  | 6 => ⟨((85438291/8589934592), (171135833/17179869184)), (119/68719476736), by norm_num⟩
  | 7 => ⟨((-760023943/274877906944), (-380588519/137438953472)), (67/137438953472), by norm_num⟩
  | 8 => ⟨((23108411/34359738368), (370295531/549755813888)), (33/274877906944), by norm_num⟩
  | 9 => ⟨((-159882281/1099511627776), (-320249703/2199023255552)), (29/1099511627776), by norm_num⟩
  | 10 => ⟨((995572971/35184372088832), (249270859/8796093022208)), (183/35184372088832), by norm_num⟩
  | 11 => ⟨((-704471109/140737488355328), (-705539919/140737488355328)), (131/140737488355328), by norm_num⟩
  | 12 => ⟨((456945827/562949953421312), (915278193/1125899906842624)), (43/281474976710656), by norm_num⟩
  | 13 => ⟨((-547184937/4503599627370496), (-548015115/4503599627370496)), (105/4503599627370496), by norm_num⟩
  | 14 => ⟨((152110389/9007199254740992), (609364671/36028797018963968)), (59/18014398509481984), by norm_num⟩
  | 15 => ⟨((-631452053/288230376151711744), (-632410079/288230376151711744)), (31/72057594037927936), by norm_num⟩
  | 16 => ⟨((614374479/2305843009213693952), (153826649/576460752303423488)), (61/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (1024056198547/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779379380989693/633825300114114700748351602688), (606354928279/316912650057057350374175801344)), (2885/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1890428680298091/39614081257132168796771975168), (170512054129/4951760157141521099596496896)), (103867/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890246553025473/2475880078570760549798248448), (181138032351/309485009821345068724781056)), (3449/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442978164784655/38685626227668133590597632), (1448825105339/154742504910672534362390528)), (55189/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550230121560529/9671406556917033397649408), (169747125789/1208925819614629174706176)), (51745/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259380640485841/604462909807314587353088), (593966715013/302231454903657293676544)), (90565/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236094211173293/9444732965739290427392), (482459036971/18889465931478580854784)), (147187/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298260436511421/4722366482869645213696), (1446891063211/4722366482869645213696)), (13801/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622439059752001/590295810358705651712), (1988685700631/590295810358705651712)), (75919/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912356344536539/36893488147419103232), (2484673412031/73786976294838206464)), (11865/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824048870003697/9223372036854775808), (349203860073/1152921504606846976)), (213629/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595296304838209/1152921504606846976), (697899710645/288230376151711744)), (106851/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195726197126743/144115188075855872), (610091198825/36028797018963968)), (187071/144115188075855872), by norm_num⟩
  | 4 => ⟨((46667285842647/1125899906842624), (3655983432309/36028797018963968)), (70193/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491398158243007/9007199254740992), (1140500775355/2251799813685248)), (351253/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116108223973077/2251799813685248), (2275029788387/1125899906842624)), (703375/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222474899578141/2251799813685248), (3397651547349/562949953421312)), (528619/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096675144916765/1125899906842624), (26943790876773/2251799813685248)), (530803/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096675144916765/1125899906842624), (26943790876773/2251799813685248)), (2024852754833030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2136095534253543/2251799813685248), (52488832417183/2251799813685248)), (1046753/562949953421312), by norm_num⟩
  | 2 => ⟨((1012556495079011/1125899906842624), (99583595169619/2251799813685248)), (8138939/2251799813685248), by norm_num⟩
  | 3 => ⟨((1816842556614455/2251799813685248), (179117194129781/2251799813685248)), (479971/70368744177664), by norm_num⟩
  | 4 => ⟨((90728366661031/140737488355328), (289037896653673/2251799813685248)), (13614039/1125899906842624), by norm_num⟩
  | 5 => ⟨((898728221907291/2251799813685248), (372664548344341/2251799813685248)), (42095831/2251799813685248), by norm_num⟩
  | 6 => ⟨((148510881650121/1125899906842624), (74368099878573/562949953421312)), (5941951/281474976710656), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1660250689/33554432)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1774179683/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-645573819183893/4503599627370496), (-760674180124473/9007199254740992)), (134418825/4503599627370496), by norm_num⟩
  | 1 => ⟨((1280243891/4294967296), (754250283/4294967296)), (269/4294967296), by norm_num⟩
  | 2 => ⟨((-1331096165/4294967296), (-392104843/2147483648)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((461322777/2147483648), (543572733/4294967296)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((-959293747/8589934592), (-565163861/8589934592)), (13/536870912), by norm_num⟩
  | 5 => ⟨((797918107/17179869184), (117522521/4294967296)), (175/17179869184), by norm_num⟩
  | 6 => ⟨((-276537343/17179869184), (-651683233/68719476736)), (245/68719476736), by norm_num⟩
  | 7 => ⟨((657192273/137438953472), (774364107/274877906944)), (147/137438953472), by norm_num⟩
  | 8 => ⟨((-683296457/549755813888), (-402561223/549755813888)), (155/549755813888), by norm_num⟩
  | 9 => ⟨((631500017/2199023255552), (372045569/2199023255552)), (289/4398046511104), by norm_num⟩
  | 10 => ⟨((-1050533895/17592186044416), (-618917609/17592186044416)), (243/17592186044416), by norm_num⟩
  | 11 => ⟨((794372299/70368744177664), (234000543/35184372088832)), (93/35184372088832), by norm_num⟩
  | 12 => ⟨((-1101233839/562949953421312), (-648787267/562949953421312)), (261/562949953421312), by norm_num⟩
  | 13 => ⟨((176150107/562949953421312), (25944523/140737488355328)), (169/2251799813685248), by norm_num⟩
  | 14 => ⟨((-418621543/9007199254740992), (-246629115/9007199254740992)), (203/18014398509481984), by norm_num⟩
  | 15 => ⟨((928532295/144115188075855872), (273520441/72057594037927936)), (57/36028797018963968), by norm_num⟩
  | 16 => ⟨((-482707157/576460752303423488), (-71096221/144115188075855872)), (15/72057594037927936), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-1699382228329/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779193863492521/633825300114114700748351602688), (-503015879707/79228162514264337593543950336)), (23149/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945109776562577/19807040628566084398385987584), (-4526408020289/39614081257132168796771975168)), (26049/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945011906856665/1237940039285380274899124224), (-2404213062227/1237940039285380274899124224)), (55369/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442922327705471/38685626227668133590597632), (-4807433422861/154742504910672534362390528)), (110771/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387505021454623/2417851639229258349412352), (-1126478544043/2417851639229258349412352)), (103883/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629598106467543/302231454903657293676544), (-3941620344795/604462909807314587353088)), (90933/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236056597967157/9444732965739290427392), (-800394496361/9444732965739290427392)), (18479/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649016849322155/2361183241434822606848), (-300039827165/295147905179352825856)), (27733/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622125576576501/590295810358705651712), (-3299032879129/295147905179352825856)), (152625/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912159130052705/36893488147419103232), (-2060841807337/18446744073709551616)), (190921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227950200190623/1152921504606846976), (-9267993676055/9223372036854775808)), (214981/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594844623590911/1152921504606846976), (-4630376148125/576460752303423488)), (26903/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195326021417151/144115188075855872), (-2023753509919/36028797018963968)), (94297/72057594037927936), by norm_num⟩
  | 4 => ⟨((746371499253259/18014398509481984), (-12126238473449/36028797018963968)), (141719/18014398509481984), by norm_num⟩
  | 3 => ⟨((372654557203083/2251799813685248), (-15129316793579/9007199254740992)), (355255/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115302538006145/2251799813685248), (-15086621445817/2251799813685248)), (356695/2251799813685248), by norm_num⟩
  | 1 => ⟨((554982455573553/562949953421312), (-22523287547431/1125899906842624)), (538649/1125899906842624), by norm_num⟩
  | 0 => ⟨((273469078232997/281474976710656), (-22310282136561/562949953421312)), (136471/140737488355328), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273469078232997/281474976710656), (-22310282136561/562949953421312)), (520595551073980287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1060995196800033/1125899906842624), (-43351436509933/562949953421312)), (2207967/1125899906842624), by norm_num⟩
  | 2 => ⟨((496577632099911/562949953421312), (-81704715724521/562949953421312)), (4501431/1125899906842624), by norm_num⟩
  | 3 => ⟨((852344627341245/1125899906842624), (-72071654006363/281474976710656)), (9248063/1125899906842624), by norm_num⟩
  | 4 => ⟨((571438177468479/1125899906842624), (-872971200407173/2251799813685248)), (18738131/1125899906842624), by norm_num⟩
  | 5 => ⟨((120811726385927/1125899906842624), (-443066980209701/1125899906842624)), (67098711/2251799813685248), by norm_num⟩
  | 6 => ⟨((-645573819183893/4503599627370496), (-760674180124473/9007199254740992)), (134418825/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1774179683/33554432)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile034Terms0

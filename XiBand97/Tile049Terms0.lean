/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile049Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨49,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15131/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15131/512))
  have he : value ((69/80), (15131/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-20060163/33554432), (-5498737781/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-79261292958665/2251799813685248), (-1235947966489859/2251799813685248)), (1548675/140737488355328), by norm_num⟩
  | 1 => ⟨((419156965/17179869184), (3268027681/8589934592)), (133/17179869184), by norm_num⟩
  | 2 => ⟨((-290537469/34359738368), (-2265224173/17179869184)), (47/17179869184), by norm_num⟩
  | 3 => ⟨((268513637/137438953472), (4187023331/137438953472)), (89/137438953472), by norm_num⟩
  | 4 => ⟨((-372238941/1099511627776), (-2902223417/549755813888)), (125/1099511627776), by norm_num⟩
  | 5 => ⟨((103206549/2199023255552), (6437337533/8796093022208)), (141/8796093022208), by norm_num⟩
  | 6 => ⟨((-190766209/35184372088832), (-5949363149/70368744177664)), (133/70368744177664), by norm_num⟩
  | 7 => ⟨((302237851/562949953421312), (4712896335/562949953421312)), (107/562949953421312), by norm_num⟩
  | 8 => ⟨((-418990629/9007199254740992), (-3266730807/4503599627370496)), (151/9007199254740992), by norm_num⟩
  | 9 => ⟨((258153043/72057594037927936), (8050934217/144115188075855872)), (189/144115188075855872), by norm_num⟩
  | 10 => ⟨((-143150443/576460752303423488), (-4464385883/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 11 => ⟨((288652585/18446744073709551616), (2250528355/9223372036854775808)), (109/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-133385817/147573952589676412928), (-4159859691/295147905179352825856)), (51/147573952589676412928), by norm_num⟩
  | 13 => ⟨((455168015/9444732965739290427392), (7097587733/9444732965739290427392)), (11/590295810358705651712), by norm_num⟩
  | 14 => ⟨((-180284815/75557863725914323419136), (-351405209/9444732965739290427392)), (141/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((266589677/2417851639229258349412352), (519627797/302231454903657293676544)), (53/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((-184785883/38685626227668133590597632), (-5762856679/77371252455336267181195264)), (149/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-2129559791295/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781045024018177/633825300114114700748351602688), (-2526365660671/633825300114114700748351602688)), (11557/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946151088754131/19807040628566084398385987584), (-710500676475/9903520314283042199192993792)), (13003/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473059179647939/618970019642690137449562112), (-3019442927989/2475880078570760549798248448)), (6909/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((13858612081163/1208925819614629174706176), (-3019234826889/154742504910672534362390528)), (13821/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552094945218377/9671406556917033397649408), (-2830311512895/9671406556917033397649408)), (405/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((630505926563827/302231454903657293676544), (-1238150701425/302231454903657293676544)), (11343/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945701728745005/37778931862957161709568), (-4023575012731/75557863725914323419136)), (18437/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81265433085987/295147905179352825856), (-188582391697/295147905179352825856)), (1729/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625169133789421/590295810358705651712), (-2074111310491/295147905179352825856)), (19027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828123251704423/73786976294838206464), (-5184393047895/73786976294838206464)), (11897/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827882962742339/9223372036854775808), (-2915612305167/4611686018427387904)), (26783/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199890863896025/144115188075855872), (-2914851040431/576460752303423488)), (13401/576460752303423488), by norm_num⟩
  | 5 => ⟨((74942128583603/9007199254740992), (-1274818923497/36028797018963968)), (23473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498367101331267/36028797018963968), (-7645484337591/36028797018963968)), (8813/9007199254740992), by norm_num⟩
  | 3 => ⟨((748825949440205/4503599627370496), (-9550849936891/9007199254740992)), (11035/2251799813685248), by norm_num⟩
  | 2 => ⟨((561170716159853/1125899906842624), (-9541832970965/2251799813685248)), (44251/2251799813685248), by norm_num⟩
  | 1 => ⟨((560268002891631/562949953421312), (-14290176547843/1125899906842624)), (66657/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115067676284691/1125899906842624), (-14244939609895/562949953421312)), (134437/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115067676284691/1125899906842624), (-14244939609895/562949953421312)), (512836460593795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((551809375738169/562949953421312), (-14107889709455/281474976710656)), (68273/281474976710656), by norm_num⟩
  | 2 => ⟨((269737527375763/281474976710656), (-55314798526903/562949953421312)), (8793/17592186044416), by norm_num⟩
  | 3 => ⟨((255771943858365/281474976710656), (-106016365335899/562949953421312)), (1189163/1125899906842624), by norm_num⟩
  | 4 => ⟨((222433342270733/281474976710656), (-96335426188295/281474976710656)), (1304521/562949953421312), by norm_num⟩
  | 5 => ⟨((285610308131713/562949953421312), (-304513190856965/562949953421312)), (5909451/1125899906842624), by norm_num⟩
  | 6 => ⟨((-79261292958665/2251799813685248), (-1235947966489859/2251799813685248)), (1548675/140737488355328), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-5498737781/268435456)), (1/134217728), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-17022057/524288)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((108391750182863/562949953421312), (-757722394669875/2251799813685248)), (28147843/2251799813685248), by norm_num⟩
  | 1 => ⟨((-454256091/2147483648), (793879637/2147483648)), (15/1073741824), by norm_num⟩
  | 2 => ⟨((1996205295/17179869184), (-872165925/4294967296)), (67/8589934592), by norm_num⟩
  | 3 => ⟨((-182754639/4294967296), (5110251749/68719476736)), (199/68719476736), by norm_num⟩
  | 4 => ⟨((803105969/68719476736), (-2807092685/137438953472)), (111/137438953472), by norm_num⟩
  | 5 => ⟨((-2823366677/1099511627776), (4934250431/1099511627776)), (99/549755813888), by norm_num⟩
  | 6 => ⟨((2067856885/4398046511104), (-3613885439/4398046511104)), (37/1099511627776), by norm_num⟩
  | 7 => ⟨((-2596311983/35184372088832), (1134359701/8796093022208)), (47/8796093022208), by norm_num⟩
  | 8 => ⟨((1426170125/140737488355328), (-4984886029/281474976710656)), (209/281474976710656), by norm_num⟩
  | 9 => ⟨((-2785436489/2251799813685248), (2433980911/1125899906842624)), (207/2251799813685248), by norm_num⟩
  | 10 => ⟨((2448091805/18014398509481984), (-4278402143/18014398509481984)), (23/2251799813685248), by norm_num⟩
  | 11 => ⟨((-1956002721/144115188075855872), (213650235/9007199254740992)), (149/144115188075855872), by norm_num⟩
  | 12 => ⟨((2865184835/2305843009213693952), (-2503666919/1152921504606846976)), (221/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-1937062935/18446744073709551616), (3385303685/18446744073709551616)), (151/18446744073709551616), by norm_num⟩
  | 14 => ⟨((38001449/4611686018427387904), (-4250441405/295147905179352825856)), (3/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-356256929/590295810358705651712), (4980892971/4722366482869645213696)), (57/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((1565552961/37778931862957161709568), (-2736035113/37778931862957161709568)), (127/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-1369136823091/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780506751034327/633825300114114700748351602688), (-50728629065/19807040628566084398385987584)), (23091/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945848392592187/19807040628566084398385987584), (-913037177711/19807040628566084398385987584)), (6495/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891593687943593/2475880078570760549798248448), (-1940016203971/2475880078570760549798248448)), (13803/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773259539257675/154742504910672534362390528), (-1939804945737/154742504910672534362390528)), (27609/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551492550993105/9671406556917033397649408), (-1818342694029/9671406556917033397649408)), (809/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1260484995610881/604462909807314587353088), (-397706359089/151115727451828646838272)), (22655/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890547759143629/75557863725914323419136), (-2584670590927/75557863725914323419136)), (9205/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162450693128881/590295810358705651712), (-969067419507/2361183241434822606848)), (27621/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812143931497827/295147905179352825856), (-2664337320751/590295810358705651712)), (9497/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1827022612023911/73786976294838206464), (-3329524677817/73786976294838206464)), (11875/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826646047378527/9223372036854775808), (-1872241085131/4611686018427387904)), (3341/576460752303423488), by norm_num⟩
  | 6 => ⟨((99868226602563/72057594037927936), (-3742941173603/1152921504606846976)), (53481/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74874688460415/9007199254740992), (-3273340412701/144115188075855872)), (46823/144115188075855872), by norm_num⟩
  | 4 => ⟨((374188050587827/9007199254740992), (-2453272829253/18014398509481984)), (35145/18014398509481984), by norm_num⟩
  | 3 => ⟨((747819841581567/4503599627370496), (-6127121245565/9007199254740992)), (43979/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120338820699483/2251799813685248), (-3059017856373/1125899906842624)), (44051/1125899906842624), by norm_num⟩
  | 1 => ⟨((279389017710417/281474976710656), (-286073741401/35184372088832)), (66257/562949953421312), by norm_num⟩
  | 0 => ⟨((554601784704071/562949953421312), (-9109032030947/562949953421312)), (33309/140737488355328), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554601784704071/562949953421312), (-9109032030947/562949953421312)), (127063751757574037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((546230021449645/562949953421312), (-17947902439949/562949953421312)), (533665/1125899906842624), by norm_num⟩
  | 2 => ⟨((529434468054443/562949953421312), (-17414839587725/281474976710656)), (1069659/1125899906842624), by norm_num⟩
  | 3 => ⟨((1983037729847767/2251799813685248), (-65512156292731/562949953421312)), (2144313/1125899906842624), by norm_num⟩
  | 4 => ⟨((1715858191551429/2251799813685248), (-230771984086021/1125899906842624)), (8551681/2251799813685248), by norm_num⟩
  | 5 => ⟨((75804543169193/140737488355328), (-703387569122383/2251799813685248)), (8269141/1125899906842624), by norm_num⟩
  | 6 => ⟨((108391750182863/562949953421312), (-757722394669875/2251799813685248)), (28147843/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-17022057/524288)), (1/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-20060163/16777216), (-5498737781/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-42224141497377/140737488355328), (87008474961461/2251799813685248)), (28127763/2251799813685248), by norm_num⟩
  | 1 => ⟨((7145396639/17179869184), (-3594737/67108864)), (75/4294967296), by norm_num⟩
  | 2 => ⟨((-4952811535/17179869184), (637870545/17179869184)), (105/8589934592), by norm_num⟩
  | 3 => ⟨((2288684901/17179869184), (-73689695/4294967296)), (49/8589934592), by norm_num⟩
  | 4 => ⟨((-3172790973/68719476736), (817244869/137438953472)), (137/68719476736), by norm_num⟩
  | 5 => ⟨((879684447/68719476736), (-906353563/549755813888)), (153/274877906944), by norm_num⟩
  | 6 => ⟨((-813001059/274877906944), (209412139/549755813888)), (285/2199023255552), by norm_num⟩
  | 7 => ⟨((2576134363/4398046511104), (-331779277/4398046511104)), (57/2199023255552), by norm_num⟩
  | 8 => ⟨((-3571280541/35184372088832), (459943741/35184372088832)), (159/35184372088832), by norm_num⟩
  | 9 => ⟨((1100188017/70368744177664), (-566771035/281474976710656)), (99/140737488355328), by norm_num⟩
  | 10 => ⟨((-2440295111/1125899906842624), (78571149/281474976710656)), (111/1125899906842624), by norm_num⟩
  | 11 => ⟨((4920679785/18014398509481984), (-316866155/9007199254740992)), (113/9007199254740992), by norm_num⟩
  | 12 => ⟨((-4547673759/144115188075855872), (585693019/144115188075855872)), (211/144115188075855872), by norm_num⟩
  | 13 => ⟨((3879639685/1152921504606846976), (-499657187/1152921504606846976)), (91/576460752303423488), by norm_num⟩
  | 14 => ⟨((-3073327211/9223372036854775808), (791625075/18446744073709551616)), (291/18446744073709551616), by norm_num⟩
  | 15 => ⟨((568071491/18446744073709551616), (-585293535/147573952589676412928)), (217/147573952589676412928), by norm_num⟩
  | 16 => ⟨((-3150057219/1180591620717411303424), (811389127/2361183241434822606848)), (303/2361183241434822606848), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (245339425081/633825300114114700748351602688)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780113467067681/633825300114114700748351602688), (4652281977433/633825300114114700748351602688)), (23165/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891253784329573/39614081257132168796771975168), (1308306585149/9903520314283042199192993792)), (6517/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945561150557505/1237940039285380274899124224), (5559620507493/2475880078570760549798248448)), (13853/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772787366971129/154742504910672534362390528), (2779426226231/77371252455336267181195264)), (27715/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775524527627673/4835703278458516698824704), (5210607952517/9671406556917033397649408)), (25993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157512012874007/75557863725914323419136), (4558465553261/604462909807314587353088)), (11377/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236239280745071/9444732965739290427392), (7405975374785/75557863725914323419136)), (36995/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299129043589077/4722366482869645213696), (1388285346619/1180591620717411303424)), (27763/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811815227169699/295147905179352825856), (3816695471565/295147905179352825856)), (38201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913098762514805/36893488147419103232), (2384617427931/18446744073709551616)), (47791/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825713255223861/9223372036854775808), (10726281532517/9223372036854775808)), (53821/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399238282046015/288230376151711744), (10720657328383/1152921504606846976)), (53891/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197167420297509/144115188075855872), (2343560924737/36028797018963968)), (47233/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495498011838751/36028797018963968), (7024346036357/18014398509481984)), (2219/1125899906842624), by norm_num⟩
  | 3 => ⟨((747024798734497/4503599627370496), (2192332858827/1125899906842624)), (89035/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118715311267965/2251799813685248), (4376328126941/562949953421312)), (89451/2251799813685248), by norm_num⟩
  | 1 => ⟨((557518794503685/562949953421312), (3271803666787/140737488355328)), (8451/70368744177664), by norm_num⟩
  | 0 => ⟨((551917892779957/562949953421312), (52013728576089/1125899906842624)), (274603/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((551917892779957/562949953421312), (52013728576089/1125899906842624)), (1047527317527389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((539900574701895/562949953421312), (50994421967487/562949953421312)), (70477/140737488355328), by norm_num⟩
  | 2 => ⟨((1026351268832707/1125899906842624), (195626041423489/1125899906842624)), (1183609/1125899906842624), by norm_num⟩
  | 3 => ⟨((450807115615729/562949953421312), (178329383110769/562949953421312)), (2569223/1125899906842624), by norm_num⟩
  | 4 => ⟨((304513190856969/562949953421312), (71402577032929/140737488355328)), (5742579/1125899906842624), by norm_num⟩
  | 5 => ⟨((39630646479335/1125899906842624), (38623373952809/70368744177664)), (6019773/562949953421312), by norm_num⟩
  | 6 => ⟨((-42224141497377/140737488355328), (87008474961461/2251799813685248)), (28127763/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-5498737781/134217728)), (1/67108864), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-2911141/2097152), (-3191918435/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-508533830771597/2251799813685248), (239036000447101/2251799813685248)), (12393719/1125899906842624), by norm_num⟩
  | 1 => ⟨((3122152813/8589934592), (-366891481/2147483648)), (153/8589934592), by norm_num⟩
  | 2 => ⟨((-2512455553/8589934592), (2361956237/17179869184)), (31/2147483648), by norm_num⟩
  | 3 => ⟨((5391521627/34359738368), (-2534281277/34359738368)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((-542332457/8589934592), (254923023/8589934592)), (217/68719476736), by norm_num⟩
  | 5 => ⟨((349140167/17179869184), (-2625809779/274877906944)), (281/274877906944), by norm_num⟩
  | 6 => ⟨((-1498451791/274877906944), (1408692603/549755813888)), (19/68719476736), by norm_num⟩
  | 7 => ⟨((5512377423/4398046511104), (-2591089465/4398046511104)), (141/2199023255552), by norm_num⟩
  | 8 => ⟨((-2217957303/8796093022208), (1042549405/8796093022208)), (229/17592186044416), by norm_num⟩
  | 9 => ⟨((3173035175/70368744177664), (-1491483145/70368744177664)), (165/70368744177664), by norm_num⟩
  | 10 => ⟨((-4085442487/562949953421312), (1920359615/562949953421312)), (215/562949953421312), by norm_num⟩
  | 11 => ⟨((4782011657/4503599627370496), (-2247781505/4503599627370496)), (127/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1282725143/9007199254740992), (2411776515/36028797018963968)), (275/36028797018963968), by norm_num⟩
  | 13 => ⟨((2540881817/144115188075855872), (-2388679729/288230376151711744)), (137/144115188075855872), by norm_num⟩
  | 14 => ⟨((-4673590317/2305843009213693952), (549204531/576460752303423488)), (127/1152921504606846976), by norm_num⟩
  | 15 => ⟨((2005827585/9223372036854775808), (-942837967/9223372036854775808)), (55/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-3228254961/147573952589676412928), (1517439169/147573952589676412928)), (179/147573952589676412928), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (1759952960717/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889909327075749/316912650057057350374175801344), (1042586268221/158456325028528675187087900672)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890922296915349/39614081257132168796771975168), (4691036650555/39614081257132168796771975168)), (13027/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890770310156235/2475880078570760549798248448), (4983517615785/2475880078570760549798248448)), (13845/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886217808621007/77371252455336267181195264), (4982720055345/154742504910672534362390528)), (13849/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550719546153593/9671406556917033397649408), (4670452599021/9671406556917033397649408)), (25977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259808038755565/604462909807314587353088), (2042899260351/302231454903657293676544)), (22739/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889446621914051/75557863725914323419136), (6637833420047/75557863725914323419136)), (36967/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298778745760727/4722366482869645213696), (2488492214597/2361183241434822606848)), (6935/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((50723421171681/18446744073709551616), (1710273401883/147573952589676412928)), (38167/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825597327681805/73786976294838206464), (4273988344109/36893488147419103232)), (47745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825039440329763/9223372036854775808), (9611811521291/9223372036854775808)), (53763/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798140535736763/576460752303423488), (4802991434209/576460752303423488)), (26913/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196581347639879/144115188075855872), (4199338316765/72057594037927936)), (737/2251799813685248), by norm_num⟩
  | 4 => ⟨((1494622854288713/36028797018963968), (6292447684353/18014398509481984)), (35447/18014398509481984), by norm_num⟩
  | 3 => ⟨((746481279954653/4503599627370496), (15708153648685/9007199254740992)), (88865/9007199254740992), by norm_num⟩
  | 2 => ⟨((279409656607529/562949953421312), (15673692892935/2251799813685248)), (89237/2251799813685248), by norm_num⟩
  | 1 => ⟨((556724201759699/562949953421312), (11712172399421/562949953421312)), (134787/1125899906842624), by norm_num⟩
  | 0 => ⟨((275190134706923/281474976710656), (46503661854551/1125899906842624)), (136657/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275190134706923/281474976710656), (46503661854551/1125899906842624)), (521305086375999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1074261722488455/1125899906842624), (90930633477051/1125899906842624)), (557001/1125899906842624), by norm_num⟩
  | 2 => ⟨((1017648070966115/1125899906842624), (43380099044487/281474976710656)), (1152881/1125899906842624), by norm_num⟩
  | 3 => ⟨((893061863084291/1125899906842624), (78418470136905/281474976710656)), (609857/281474976710656), by norm_num⟩
  | 4 => ⟨((1241972192569887/2251799813685248), (248805580727251/562949953421312)), (2614571/562949953421312), by norm_num⟩
  | 5 => ⟨((1915229971493/17592186044416), (1097822677633957/2251799813685248)), (20780903/2251799813685248), by norm_num⟩
  | 6 => ⟨((-508533830771597/2251799813685248), (239036000447101/2251799813685248)), (12393719/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-3191918435/67108864)), (1/67108864), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-7107015483/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-431153129061649/2251799813685248), (-211301284278191/2251799813685248)), (21276757/2251799813685248), by norm_num⟩
  | 1 => ⟨((1473470119/4294967296), (1444248493/8589934592)), (147/8589934592), by norm_num⟩
  | 2 => ⟨((-5280208077/17179869184), (-2587745913/17179869184)), (265/17179869184), by norm_num⟩
  | 3 => ⟨((3153620941/17179869184), (1545539415/17179869184)), (5/536870912), by norm_num⟩
  | 4 => ⟨((-706316273/8589934592), (-1384617441/34359738368)), (289/68719476736), by norm_num⟩
  | 5 => ⟨((2024878193/68719476736), (1984721129/137438953472)), (209/137438953472), by norm_num⟩
  | 6 => ⟨((-4837459569/549755813888), (-1185380959/274877906944)), (63/137438953472), by norm_num⟩
  | 7 => ⟨((4952893709/2199023255552), (151708397/137438953472)), (65/549755813888), by norm_num⟩
  | 8 => ⟨((-2218598551/4398046511104), (-2174599655/8796093022208)), (235/8796093022208), by norm_num⟩
  | 9 => ⟨((3533506633/35184372088832), (108232209/2199023255552)), (189/35184372088832), by norm_num⟩
  | 10 => ⟨((-633119397/35184372088832), (-2482253893/281474976710656)), (273/281474976710656), by norm_num⟩
  | 11 => ⟨((3300065963/1125899906842624), (404327447/281474976710656)), (179/1125899906842624), by norm_num⟩
  | 12 => ⟨((-1970974813/4503599627370496), (-60371461/281474976710656)), (27/1125899906842624), by norm_num⟩
  | 13 => ⟨((2173238637/36028797018963968), (133133707/4503599627370496)), (15/4503599627370496), by norm_num⟩
  | 14 => ⟨((-2225097661/288230376151711744), (-545242469/144115188075855872)), (247/576460752303423488), by norm_num⟩
  | 15 => ⟨((4252629125/4611686018427387904), (521036457/1152921504606846976)), (119/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-952461063/9223372036854775808), (-1867144011/36893488147419103232)), (215/36893488147419103232), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-3498696619239/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889788053287033/316912650057057350374175801344), (-4144141962561/633825300114114700748351602688)), (1447/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1890649477053727/39614081257132168796771975168), (-4661499526023/39614081257132168796771975168)), (26053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472620122795191/618970019642690137449562112), (-1238014888189/618970019642690137449562112)), (27689/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772145856950389/154742504910672534362390528), (-1237794451175/38685626227668133590597632)), (13849/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775223979127267/4835703278458516698824704), (-2320396167791/4835703278458516698824704)), (3247/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259570461743831/604462909807314587353088), (-2029878219141/302231454903657293676544)), (11369/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889060676324205/75557863725914323419136), (-6595347610823/75557863725914323419136)), (36965/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162311173630629/590295810358705651712), (-618121710585/590295810358705651712)), (27739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101421986164741/36893488147419103232), (-3398420579677/295147905179352825856)), (19083/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825100454225907/73786976294838206464), (-8492304975675/73786976294838206464)), (47743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824480801889531/9223372036854775808), (-4774345859605/4611686018427387904)), (105/18014398509481984), by norm_num⟩
  | 6 => ⟨((797861431855159/576460752303423488), (-2385563133851/288230376151711744)), (26911/576460752303423488), by norm_num⟩
  | 5 => ⟨((598046700473985/72057594037927936), (-4171113474563/72057594037927936)), (47165/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493891905919935/36028797018963968), (-12498852566505/36028797018963968)), (8861/4503599627370496), by norm_num⟩
  | 3 => ⟨((1492050578154625/9007199254740992), (-15598212436365/9007199254740992)), (11107/1125899906842624), by norm_num⟩
  | 2 => ⟨((1116729206765687/2251799813685248), (-15560183659723/2251799813685248)), (44613/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112090701926587/1125899906842624), (-23245208289577/1125899906842624)), (67383/562949953421312), by norm_num⟩
  | 0 => ⟨((274517745473015/281474976710656), (-11527545619053/281474976710656)), (68313/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274517745473015/281474976710656), (-11527545619053/281474976710656)), (260593415380382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((66815094143269/70368744177664), (-44970474763485/562949953421312)), (555379/1125899906842624), by norm_num⟩
  | 2 => ⟨((62991854386735/70368744177664), (-170797790416927/1125899906842624)), (285849/281474976710656), by norm_num⟩
  | 3 => ⟨((876302929662635/1125899906842624), (-305785463965525/1125899906842624)), (149623/70368744177664), by norm_num⟩
  | 4 => ⟨((299494684413795/562949953421312), (-475993818442855/1125899906842624)), (78545/17592186044416), by norm_num⟩
  | 5 => ⟨((234866612865163/2251799813685248), (-506466401039987/1125899906842624)), (4799549/562949953421312), by norm_num⟩
  | 6 => ⟨((-431153129061649/2251799813685248), (-211301284278191/2251799813685248)), (21276757/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-7107015483/134217728)), (1/67108864), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-225263989/134217728), (-7718454287/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((483353835558351/4503599627370496), (-687907031876637/4503599627370496)), (6541303/1125899906842624), by norm_num⟩
  | 1 => ⟨((-112123863/536870912), (2553186941/8589934592)), (49/4294967296), by norm_num⟩
  | 2 => ⟨((3490927407/17179869184), (-4968272381/17179869184)), (193/17179869184), by norm_num⟩
  | 3 => ⟨((-1132171845/8589934592), (3222603883/17179869184)), (127/17179869184), by norm_num⟩
  | 4 => ⟨((550776171/8589934592), (-3135448801/34359738368)), (125/34359738368), by norm_num⟩
  | 5 => ⟨((-3429635011/137438953472), (4881041315/137438953472)), (49/34359738368), by norm_num⟩
  | 6 => ⟨((278073399/34359738368), (-3166022611/274877906944)), (129/274877906944), by norm_num⟩
  | 7 => ⟨((-618406685/274877906944), (3520454589/1099511627776)), (145/1099511627776), by norm_num⟩
  | 8 => ⟨((2406727689/4398046511104), (-3425244157/4398046511104)), (71/2199023255552), by norm_num⟩
  | 9 => ⟨((-2081455927/17592186044416), (1481159415/8796093022208)), (31/4398046511104), by norm_num⟩
  | 10 => ⟨((1620130485/70368744177664), (-4611525021/140737488355328)), (195/140737488355328), by norm_num⟩
  | 11 => ⟨((-2292820621/562949953421312), (815783031/140737488355328)), (139/562949953421312), by norm_num⟩
  | 12 => ⟨((1487207639/2251799813685248), (-1058293653/1125899906842624)), (91/2251799813685248), by norm_num⟩
  | 13 => ⟨((-445226529/4503599627370496), (1267288837/9007199254740992)), (55/9007199254740992), by norm_num⟩
  | 14 => ⟨((1980276163/144115188075855872), (-176145015/9007199254740992)), (31/36028797018963968), by norm_num⟩
  | 15 => ⟨((-2055167725/1152921504606846976), (1462452789/576460752303423488)), (131/1152921504606846976), by norm_num⟩
  | 16 => ⟨((1999585867/9223372036854775808), (-2845801725/9223372036854775808)), (129/9223372036854775808), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532090827/10141204801825835211973625643008), (-1248290119141/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((6950699214767/2475880078570760549798248448), (-739126296709/316912650057057350374175801344)), (23087/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890428228541015/39614081257132168796771975168), (-831393694611/19807040628566084398385987584)), (25975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236280755613921/309485009821345068724781056), (-1766409009669/2475880078570760549798248448)), (27601/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771912119406963/154742504910672534362390528), (-220758584791/19342813113834066795298816)), (6901/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550229581985735/9671406556917033397649408), (-827663933355/4835703278458516698824704)), (12941/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259380134800979/604462909807314587353088), (-362012614331/151115727451828646838272)), (11325/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472188201192633/18889465931478580854784), (-2352404517259/75557863725914323419136)), (9203/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298259718072677/4722366482869645213696), (-881855397213/2361183241434822606848)), (27615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811218991319329/295147905179352825856), (-1212069874393/295147905179352825856)), (37979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824711208926593/73786976294838206464), (-3028731444519/73786976294838206464)), (47487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824047021145735/9223372036854775808), (-1702669736005/4611686018427387904)), (835/144115188075855872), by norm_num⟩
  | 6 => ⟨((1595294226693021/1152921504606846976), (-3402861798269/1152921504606846976)), (26731/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195724121253779/144115188075855872), (-1487359430931/72057594037927936)), (46805/144115188075855872), by norm_num⟩
  | 4 => ⟨((746674759646223/18014398509481984), (-557064161745/4503599627370496)), (4391/2251799813685248), by norm_num⟩
  | 3 => ⟨((1491392726929057/9007199254740992), (-2780457531829/4503599627370496)), (21977/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232202905272347/4503599627370496), (-11092699188777/4503599627370496)), (11005/281474976710656), by norm_num⟩
  | 1 => ⟨((2222447920799347/2251799813685248), (-16566391724745/2251799813685248)), (132391/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096634942279641/1125899906842624), (-32843175009299/2251799813685248)), (532221/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096634942279641/1125899906842624), (-32843175009299/2251799813685248)), (2030262001998137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((533945566912885/562949953421312), (-63978996910313/2251799813685248)), (1052301/2251799813685248), by norm_num⟩
  | 2 => ⟨((252990549774407/281474976710656), (-60682662052249/1125899906842624)), (1027983/1125899906842624), by norm_num⟩
  | 3 => ⟨((906284031757529/1125899906842624), (-218167031595911/2251799813685248)), (3917439/2251799813685248), by norm_num⟩
  | 4 => ⟨((718937383226005/1125899906842624), (-175611789102805/1125899906842624)), (3532855/1125899906842624), by norm_num⟩
  | 5 => ⟨((215841327268137/562949953421312), (-448543886908253/2251799813685248)), (5613843/1125899906842624), by norm_num⟩
  | 6 => ⟨((483353835558351/4503599627370496), (-687907031876637/4503599627370496)), (6541303/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-225263989/134217728), (-7718454287/134217728)), (1/67108864), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-240721955/134217728), (-515506667/8388608)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((71536462428169/2251799813685248), (1470988789395175/9007199254740992)), (84443833/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1134917387/17179869184), (-5834265129/17179869184)), (169/8589934592), by norm_num⟩
  | 2 => ⟨((1179997181/17179869184), (3033003319/8589934592)), (177/8589934592), by norm_num⟩
  | 3 => ⟨((-817911719/17179869184), (-4204635399/17179869184)), (247/17179869184), by norm_num⟩
  | 4 => ⟨((850399803/34359738368), (2185823379/17179869184)), (259/34359738368), by norm_num⟩
  | 5 => ⟨((-707342671/68719476736), (-1818116775/34359738368)), (217/68719476736), by norm_num⟩
  | 6 => ⟨((245146289/68719476736), (2520445033/137438953472)), (303/274877906944), by norm_num⟩
  | 7 => ⟨((-72823911/68719476736), (-5989849263/1099511627776)), (363/1099511627776), by norm_num⟩
  | 8 => ⟨((605732263/2199023255552), (6227770693/4398046511104)), (95/1099511627776), by norm_num⟩
  | 9 => ⟨((-1119630961/17592186044416), (-5755682263/17592186044416)), (353/17592186044416), by norm_num⟩
  | 10 => ⟨((931282853/70368744177664), (18700945/274877906944)), (37/8796093022208), by norm_num⟩
  | 11 => ⟨((-176049841/70368744177664), (-1810037383/140737488355328)), (113/140737488355328), by norm_num⟩
  | 12 => ⟨((976227607/2251799813685248), (5018489235/2251799813685248)), (79/562949953421312), by norm_num⟩
  | 13 => ⟨((-9759655/140737488355328), (-3210970767/9007199254740992)), (407/18014398509481984), by norm_num⟩
  | 14 => ⟨((371101843/36028797018963968), (1907721715/36028797018963968)), (243/72057594037927936), by norm_num⟩
  | 15 => ⟨((-205782557/144115188075855872), (-2115731085/288230376151711744)), (271/576460752303423488), by norm_num⟩
  | 16 => ⟨((855825595/4611686018427387904), (4399539109/4611686018427387904)), (71/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509236873/10141204801825835211973625643008), (1795871005149/10141204801825835211973625643008)), (7279/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889600052903293/316912650057057350374175801344), (265788243059/79228162514264337593543950336)), (17327/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945113466536265/19807040628566084398385987584), (2391714280099/39614081257132168796771975168)), (38991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472508028541595/618970019642690137449562112), (2540731165025/2475880078570760549798248448)), (20717/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771698127626025/154742504910672534362390528), (1270103934365/77371252455336267181195264)), (1295/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((387507224973123/2417851639229258349412352), (1190444498695/4835703278458516698824704)), (38857/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157400559153673/75557863725914323419136), (2082722131253/604462909807314587353088)), (34007/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944233616726823/37778931862957161709568), (1691690870707/37778931862957161709568)), (27637/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649022716802121/2361183241434822606848), (1268312546365/2361183241434822606848)), (41467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622143169508889/590295810358705651712), (3486379330661/590295810358705651712)), (14259/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456085608735861/18446744073709551616), (4355754867485/73786976294838206464)), (71323/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823631796916355/9223372036854775808), (4897174256769/9223372036854775808)), (20069/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797439280791111/576460752303423488), (4893364138411/1152921504606846976)), (20081/288230376151711744), by norm_num⟩
  | 5 => ⟨((597679959825925/72057594037927936), (4277410458289/144115188075855872)), (35169/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492802231028537/36028797018963968), (800944676051/4503599627370496)), (105615/36028797018963968), by norm_num⟩
  | 3 => ⟨((745353449488003/4503599627370496), (3997243932755/4503599627370496)), (8263/562949953421312), by norm_num⟩
  | 2 => ⟨((2230826126961261/4503599627370496), (1993021420151/562949953421312)), (264985/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220370053631763/2251799813685248), (11902249479715/1125899906842624)), (199453/1125899906842624), by norm_num⟩
  | 0 => ⟨((2189063986780033/2251799813685248), (11790870138259/562949953421312)), (401771/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189063986780033/2251799813685248), (11790870138259/562949953421312)), (1532634739402389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2127088169743015/2251799813685248), (91698983313161/2251799813685248)), (1595971/2251799813685248), by norm_num⟩
  | 2 => ⟨((1002774614082829/1125899906842624), (86620409770649/1125899906842624)), (3145147/2251799813685248), by norm_num⟩
  | 3 => ⟨((886449874624279/1125899906842624), (308591367497467/2251799813685248)), (6086345/2251799813685248), by norm_num⟩
  | 4 => ⟨((676779718665009/1125899906842624), (121480949312531/562949953421312)), (11252043/2251799813685248), by norm_num⟩
  | 5 => ⟨((708766917890091/2251799813685248), (584178697940935/2251799813685248)), (18383469/2251799813685248), by norm_num⟩
  | 6 => ⟨((71536462428169/2251799813685248), (1470988789395175/9007199254740992)), (84443833/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-240721955/134217728), (-515506667/8388608)), (3/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile049Terms0

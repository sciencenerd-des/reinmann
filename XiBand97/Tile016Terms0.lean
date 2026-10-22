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
namespace Reinmann.XiBand97.Tile016Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53459/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53459/2560))
  have he : value ((69/80), (53459/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1942746831/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-205005681480545/1125899906842624), (-584324484057175/1125899906842624)), (52714413/2251799813685248), by norm_num⟩
  | 1 => ⟨((542065087/4294967296), (772519815/2147483648)), (9/536870912), by norm_num⟩
  | 2 => ⟨((-375730887/8589934592), (-1070939863/8589934592)), (13/2147483648), by norm_num⟩
  | 3 => ⟨((347249073/34359738368), (247439649/8589934592)), (25/17179869184), by norm_num⟩
  | 4 => ⟨((-60173679/34359738368), (-1372096761/274877906944)), (9/34359738368), by norm_num⟩
  | 5 => ⟨((133469491/549755813888), (760852001/1099511627776)), (41/1099511627776), by norm_num⟩
  | 6 => ⟨((-493408007/17592186044416), (-703176559/8796093022208)), (39/8796093022208), by norm_num⟩
  | 7 => ⟨((48857767/17592186044416), (1114068227/140737488355328)), (63/140737488355328), by norm_num⟩
  | 8 => ⟨((-541849975/2251799813685248), (-1544426501/2251799813685248)), (89/2251799813685248), by norm_num⟩
  | 9 => ⟨((333850473/18014398509481984), (475784389/9007199254740992)), (57/18014398509481984), by norm_num⟩
  | 10 => ⟨((-370252023/288230376151711744), (-1055323545/288230376151711744)), (65/288230376151711744), by norm_num⟩
  | 11 => ⟨((373293303/4611686018427387904), (531996029/2305843009213693952)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-344996267/73786976294838206464), (-245834365/18446744073709551616)), (1/1152921504606846976), by norm_num⟩
  | 13 => ⟨((73579443/295147905179352825856), (838889339/1180591620717411303424)), (7/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-466298363/37778931862957161709568), (-664541463/18889465931478580854784)), (91/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((344760955/604462909807314587353088), (982666755/604462909807314587353088)), (69/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-59742521/2417851639229258349412352), (-1362265381/19342813113834066795298816)), (49/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-2485671205333/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((27828809247903/9903520314283042199192993792), (-2948832149509/633825300114114700748351602688)), (23123/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236537589560675/4951760157141521099596496896), (-829312169433/9903520314283042199192993792)), (13009/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118264692192551/154742504910672534362390528), (-3524360564009/2475880078570760549798248448)), (27649/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773900600319255/154742504910672534362390528), (-3524117323797/154742504910672534362390528)), (3457/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552093199329683/9671406556917033397649408), (-825900373065/2417851639229258349412352)), (12967/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157626277068659/75557863725914323419136), (-2890392743871/604462909807314587353088)), (22699/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891400593862479/75557863725914323419136), (-4696403271381/75557863725914323419136)), (1153/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1300244603039129/4722366482869645213696), (-880469499861/1180591620717411303424)), (27683/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406291411228969/147573952589676412928), (-1210473065125/147573952589676412928)), (38081/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914059227764903/36893488147419103232), (-6051329903865/73786976294838206464)), (47627/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456969242266133/2305843009213693952), (-6806321724677/9223372036854775808)), (53615/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599120170399947/1152921504606846976), (-1701135033957/288230376151711744)), (13415/288230376151711744), by norm_num⟩
  | 5 => ⟨((74941707451263/9007199254740992), (-5951966865353/144115188075855872)), (23501/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498355315594773/36028797018963968), (-1115491891347/4503599627370496)), (35301/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497634232225445/9007199254740992), (-5573942074247/4503599627370496)), (22107/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122319369939437/2251799813685248), (-5568657794873/1125899906842624)), (88689/2251799813685248), by norm_num⟩
  | 1 => ⟨((560245971971527/562949953421312), (-16679494697995/1125899906842624)), (133689/1125899906842624), by norm_num⟩
  | 0 => ⟨((69683487881147/70368744177664), (-33252732109069/1125899906842624)), (67501/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((69683487881147/70368744177664), (-33252732109069/1125899906842624)), (257495881200694949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((34471761765283/35184372088832), (-65857828841937/1125899906842624)), (550699/1125899906842624), by norm_num⟩
  | 2 => ⟨((1076902444733029/1125899906842624), (-32261985242855/281474976710656)), (285879/281474976710656), by norm_num⟩
  | 3 => ⟨((1015246113314393/1125899906842624), (-61715984820359/281474976710656)), (2449639/1125899906842624), by norm_num⟩
  | 4 => ⟨((861340213449353/1125899906842624), (-445204148876425/1125899906842624)), (1372997/281474976710656), by norm_num⟩
  | 5 => ⟨((120725702574419/281474976710656), (-340591765121585/562949953421312)), (12746295/1125899906842624), by norm_num⟩
  | 6 => ⟨((-205005681480545/1125899906842624), (-584324484057175/1125899906842624)), (52714413/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1942746831/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-769795219/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-507426329900767/2251799813685248), (44398853238241/140737488355328)), (38723769/1125899906842624), by norm_num⟩
  | 1 => ⟨((66454983/268435456), (-744279873/2147483648)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-73008261/536870912), (817675015/4294967296)), (93/4294967296), by norm_num⟩
  | 3 => ⟨((106943697/2147483648), (-74858985/1073741824)), (139/17179869184), by norm_num⟩
  | 4 => ⟨((-469958639/34359738368), (657928007/34359738368)), (39/17179869184), by norm_num⟩
  | 5 => ⟨((413041869/137438953472), (-578246235/137438953472)), (35/68719476736), by norm_num⟩
  | 6 => ⟨((-302515249/549755813888), (52939035/68719476736)), (105/1099511627776), by norm_num⟩
  | 7 => ⟨((759650217/8796093022208), (-265871883/2199023255552)), (135/8796093022208), by norm_num⟩
  | 8 => ⟨((-104320133/8796093022208), (146045059/8796093022208)), (151/70368744177664), by norm_num⟩
  | 9 => ⟨((407492907/281474976710656), (-1140955709/562949953421312)), (75/281474976710656), by norm_num⟩
  | 10 => ⟨((-89535343/562949953421312), (501387185/2251799813685248)), (135/4503599627370496), by norm_num⟩
  | 11 => ⟨((572303291/36028797018963968), (-200301863/9007199254740992)), (55/18014398509481984), by norm_num⟩
  | 12 => ⟨((-419159619/288230376151711744), (293405451/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 13 => ⟨((566761733/4611686018427387904), (-396724719/2305843009213693952)), (113/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-711601605/73786976294838206464), (498110459/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 15 => ⟨((833892553/1180591620717411303424), (-1167424579/1180591620717411303424)), (43/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-458062303/9444732965739290427392), (320636747/4722366482869645213696)), (97/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (1427047496981/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890251024725019/316912650057057350374175801344), (1691977880639/316912650057057350374175801344)), (46267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891691215104791/39614081257132168796771975168), (3806614368267/39614081257132168796771975168)), (52061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945793711211061/1237940039285380274899124224), (4044135061969/2475880078570760549798248448)), (55327/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886626441555001/77371252455336267181195264), (63182706061/2417851639229258349412352)), (13835/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551485895935531/9671406556917033397649408), (3790492820211/9671406556917033397649408)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260478757652657/604462909807314587353088), (829052903867/151115727451828646838272)), (2839/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1890536845033283/75557863725914323419136), (673495405779/9444732965739290427392)), (36921/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299596679488199/4722366482869645213696), (4040201759791/4722366482869645213696)), (27703/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624274568482135/590295810358705651712), (5554024839743/590295810358705651712)), (76223/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827004338244221/73786976294838206464), (6940651772123/73786976294838206464)), (95337/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826623214418807/9223372036854775808), (7805648575873/9223372036854775808)), (107335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597865951301025/1152921504606846976), (3901208375805/576460752303423488)), (107437/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598984678475995/72057594037927936), (426467343637/9007199254740992)), (47061/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496707335959573/36028797018963968), (10227938545833/36028797018963968)), (141411/36028797018963968), by norm_num⟩
  | 3 => ⟨((93473278453001/562949953421312), (12772179622659/9007199254740992)), (177165/9007199254740992), by norm_num⟩
  | 2 => ⟨((560127455621353/1125899906842624), (3188262297619/562949953421312)), (177767/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117388628279341/1125899906842624), (19081695201899/1125899906842624)), (268159/1125899906842624), by norm_num⟩
  | 0 => ⟨((277175780936317/281474976710656), (18985781807783/562949953421312)), (271181/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277175780936317/281474976710656), (18985781807783/562949953421312)), (1034473421336936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1090488390217729/1125899906842624), (74783186210805/1125899906842624)), (276185/281474976710656), by norm_num⟩
  | 2 => ⟨((1051223467616159/1125899906842624), (72431124517157/562949953421312)), (2286745/1125899906842624), by norm_num⟩
  | 3 => ⟨((962861530659309/1125899906842624), (270508230493731/1125899906842624)), (4858591/1125899906842624), by norm_num⟩
  | 4 => ⟨((189610022007511/281474976710656), (462673399804343/1125899906842624)), (10644711/1125899906842624), by norm_num⟩
  | 5 => ⟨((641557371218425/2251799813685248), (1246682949147149/2251799813685248)), (46179595/2251799813685248), by norm_num⟩
  | 6 => ⟨((-507426329900767/2251799813685248), (44398853238241/140737488355328)), (38723769/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-769795219/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1942746831/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1063710091491195/4503599627370496), (851157999618885/4503599627370496)), (30522975/1125899906842624), by norm_num⟩
  | 1 => ⟨((351575685/1073741824), (-140661661/536870912)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-974774779/4294967296), (389996935/2147483648)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((450441593/4294967296), (-720867403/8589934592)), (55/4294967296), by norm_num⟩
  | 4 => ⟨((-19513895/536870912), (62458401/2147483648)), (39/8589934592), by norm_num⟩
  | 5 => ⟨((692531267/68719476736), (-277074333/34359738368)), (89/68719476736), by norm_num⟩
  | 6 => ⟨((-320017397/137438953472), (256071057/137438953472)), (21/68719476736), by norm_num⟩
  | 7 => ⟨((507015215/1099511627776), (-101425675/274877906944)), (135/2199023255552), by norm_num⟩
  | 8 => ⟨((-351436167/4398046511104), (562423365/8796093022208)), (3/274877906944), by norm_num⟩
  | 9 => ⟨((866122625/70368744177664), (-346526373/35184372088832)), (15/8796093022208), by norm_num⟩
  | 10 => ⟨((-960560729/562949953421312), (768620091/562949953421312)), (135/562949953421312), by norm_num⟩
  | 11 => ⟨((968450853/4503599627370496), (-774933599/4503599627370496)), (139/4503599627370496), by norm_num⟩
  | 12 => ⟨((-447519319/18014398509481984), (716190719/36028797018963968)), (65/18014398509481984), by norm_num⟩
  | 13 => ⟨((763561241/288230376151711744), (-305492663/144115188075855872)), (113/288230376151711744), by norm_num⟩
  | 14 => ⟨((-604868939/2305843009213693952), (242001575/1152921504606846976)), (91/2305843009213693952), by norm_num⟩
  | 15 => ⟨((894428159/36893488147419103232), (-715702227/36893488147419103232)), (137/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-619970357/295147905179352825856), (496086981/295147905179352825856)), (97/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (803301993305/2535301200456458802993406410752)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780117278747223/633825300114114700748351602688), (1904090315211/316912650057057350374175801344)), (2893/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((59101821792089/1237940039285380274899124224), (4283728716163/39614081257132168796771975168)), (52085/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236390922175123/309485009821345068724781056), (2275452107095/1237940039285380274899124224)), (55355/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886396379765631/77371252455336267181195264), (2275138434271/77371252455336267181195264)), (27685/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775527223348559/4835703278458516698824704), (1066304490027/2417851639229258349412352)), (51927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630050578140121/302231454903657293676544), (3731399055357/604462909807314587353088)), (11363/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889923086837459/75557863725914323419136), (6062273360053/75557863725914323419136)), (73891/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299136224572191/4722366482869645213696), (4545611060615/4722366482869645213696)), (27723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623641221911661/590295810358705651712), (3124218652133/295147905179352825856)), (38141/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913106162049069/36893488147419103232), (7807879390285/73786976294838206464)), (95419/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825731744541163/9223372036854775808), (8780196237189/9223372036854775808)), (53719/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798486957786423/576460752303423488), (68559454781/9007199254740992)), (3361/36028797018963968), by norm_num⟩
  | 5 => ⟨((598594095655847/72057594037927936), (3836749192709/72057594037927936)), (94237/144115188075855872), by norm_num⟩
  | 4 => ⟨((747767162124233/18014398509481984), (11499923316381/36028797018963968)), (141613/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494103992297979/9007199254740992), (14356829621989/9007199254740992)), (177469/9007199254740992), by norm_num⟩
  | 2 => ⟨((559391587777799/1125899906842624), (7164851913203/1125899906842624)), (44537/562949953421312), by norm_num⟩
  | 1 => ⟨((278793232336333/281474976710656), (10713346378017/562949953421312)), (268921/1125899906842624), by norm_num⟩
  | 0 => ⟨((69014991373797/70368744177664), (21290823468035/562949953421312)), (136165/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((69014991373797/70368744177664), (21290823468035/562949953421312)), (519428254247569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((135173258823005/140737488355328), (652538466811/8796093022208)), (1109563/1125899906842624), by norm_num⟩
  | 2 => ⟨((258108961041047/281474976710656), (20055665815155/140737488355328)), (2296017/1125899906842624), by norm_num⟩
  | 3 => ⟨((923866378521609/1125899906842624), (294252633155799/1125899906842624)), (4865221/1125899906842624), by norm_num⟩
  | 4 => ⟨((681183530243167/1125899906842624), (482902810297673/1125899906842624)), (5263717/562949953421312), by norm_num⟩
  | 5 => ⟨((6406427546267/35184372088832), (1168648968114337/2251799813685248)), (21768973/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1063710091491195/4503599627370496), (851157999618885/4503599627370496)), (30522975/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1942746831/67108864)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-281932403/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-655026932154553/4503599627370496), (-57074484788387/281474976710656)), (100407143/2251799813685248), by norm_num⟩
  | 1 => ⟨((251346869/1073741824), (175204925/536870912)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-101131795/536870912), (-1127925795/4294967296)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((54255115/536870912), (1210217691/8589934592)), (137/4294967296), by norm_num⟩
  | 4 => ⟨((-87320239/2147483648), (-973885117/17179869184)), (223/17179869184), by norm_num⟩
  | 5 => ⟨((224858405/17179869184), (156740763/8589934592)), (145/34359738368), by norm_num⟩
  | 6 => ⟨((-482527523/137438953472), (-168176351/34359738368)), (157/137438953472), by norm_num⟩
  | 7 => ⟨((443770337/549755813888), (1237345807/1099511627776)), (291/1099511627776), by norm_num⟩
  | 8 => ⟨((-714220805/4398046511104), (-497857813/2199023255552)), (59/1099511627776), by norm_num⟩
  | 9 => ⟨((510886241/17592186044416), (356120551/8796093022208)), (171/17592186044416), by norm_num⟩
  | 10 => ⟨((-164447937/35184372088832), (-458523133/70368744177664)), (111/70368744177664), by norm_num⟩
  | 11 => ⟨((384972719/562949953421312), (536701465/562949953421312)), (131/562949953421312), by norm_num⟩
  | 12 => ⟨((-413059793/4503599627370496), (-575858457/4503599627370496)), (283/9007199254740992), by norm_num⟩
  | 13 => ⟨((51138007/4503599627370496), (570343651/36028797018963968)), (141/36028797018963968), by norm_num⟩
  | 14 => ⟨((-752488661/576460752303423488), (-1049065937/576460752303423488)), (131/288230376151711744), by norm_num⟩
  | 15 => ⟨((645911349/4611686018427387904), (450241731/2305843009213693952)), (227/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-519777107/36893488147419103232), (-45289757/2305843009213693952)), (23/4611686018427387904), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-2856672846139/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779821824733501/633825300114114700748351602688), (-423069245125/79228162514264337593543950336)), (92533/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890926049087301/39614081257132168796771975168), (-3807141787301/39614081257132168796771975168)), (104121/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890774530542133/2475880078570760549798248448), (-4044513694921/2475880078570760549798248448)), (110653/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886220050222501/77371252455336267181195264), (-4043867414697/154742504910672534362390528)), (110681/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550724028279753/9671406556917033397649408), (-1895219527099/4835703278458516698824704)), (103793/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259812239604697/604462909807314587353088), (-1657973777071/302231454903657293676544)), (90849/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472363492777931/18889465931478580854784), (-2693563713775/37778931862957161709568)), (36921/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298784714838521/4722366482869645213696), (-4039219202733/4722366482869645213696)), (27703/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623158427356129/590295810358705651712), (-2776048085777/295147905179352825856)), (152445/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825609627641601/73786976294838206464), (-6937375069281/73786976294838206464)), (95337/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825054806127971/9223372036854775808), (-3900386354881/4611686018427387904)), (214671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798149172706451/576460752303423488), (-7796055405207/1152921504606846976)), (214875/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598299302924697/72057594037927936), (-6816242202351/144115188075855872)), (188245/144115188075855872), by norm_num⟩
  | 4 => ⟨((373663255190567/9007199254740992), (-10213752486305/36028797018963968)), (141413/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493007738831357/9007199254740992), (-3187156404255/2251799813685248)), (11073/281474976710656), by norm_num⟩
  | 2 => ⟨((1117694976198971/2251799813685248), (-6360393042811/1125899906842624)), (44443/281474976710656), by norm_num⟩
  | 1 => ⟨((278390182847885/281474976710656), (-19011608484855/1125899906842624)), (536339/1125899906842624), by norm_num⟩
  | 0 => ⟨((137636958004625/140737488355328), (-37745106239505/1125899906842624)), (542401/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((137636958004625/140737488355328), (-37745106239505/1125899906842624)), (2069095613719749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1075572491796395/1125899906842624), (-73827118319043/1125899906842624)), (1097271/562949953421312), by norm_num⟩
  | 2 => ⟨((3994741141037/4398046511104), (-17631766627293/140737488355328)), (2240347/562949953421312), by norm_num⟩
  | 3 => ⟨((455601950543147/562949953421312), (-256238649072513/1125899906842624)), (4631157/562949953421312), by norm_num⟩
  | 4 => ⟨((679131687843059/1125899906842624), (-829507686162699/2251799813685248)), (19208137/1125899906842624), by norm_num⟩
  | 5 => ⟨((256860398801185/1125899906842624), (-1000701663724727/2251799813685248)), (4665491/140737488355328), by norm_num⟩
  | 6 => ⟨((-655026932154553/4503599627370496), (-57074484788387/281474976710656)), (100407143/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-281932403/8388608)), (1/16777216), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1255481927/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((461070003390419/2251799813685248), (66999450391053/1125899906842624)), (37954613/4503599627370496), by norm_num⟩
  | 1 => ⟨((-196963917/536870912), (-114485645/1073741824)), (67/4294967296), by norm_num⟩
  | 2 => ⟨((705823927/2147483648), (410261477/4294967296)), (31/2147483648), by norm_num⟩
  | 3 => ⟨((-843111137/4294967296), (-122514981/2147483648)), (39/4294967296), by norm_num⟩
  | 4 => ⟨((377663091/4294967296), (439034755/17179869184)), (9/2147483648), by norm_num⟩
  | 5 => ⟨((-1082690271/34359738368), (-19666117/2147483648)), (53/34359738368), by norm_num⟩
  | 6 => ⟨((323320091/34359738368), (375860815/137438953472)), (65/137438953472), by norm_num⟩
  | 7 => ⟨((-1324141337/549755813888), (-192414907/274877906944)), (17/137438953472), by norm_num⟩
  | 8 => ⟨((593135695/1099511627776), (21547577/137438953472)), (63/2199023255552), by norm_num⟩
  | 9 => ⟨((-944672443/8796093022208), (-34318289/1099511627776)), (51/8796093022208), by norm_num⟩
  | 10 => ⟨((338525159/17592186044416), (393536763/70368744177664)), (75/70368744177664), by norm_num⟩
  | 11 => ⟨((-882262777/281474976710656), (-64102111/70368744177664)), (25/140737488355328), by norm_num⟩
  | 12 => ⟨((1053868457/2251799813685248), (306281505/2251799813685248)), (61/2251799813685248), by norm_num⟩
  | 13 => ⟨((-1162017715/18014398509481984), (-84428121/4503599627370496)), (69/18014398509481984), by norm_num⟩
  | 14 => ⟨((594873213/72057594037927936), (172885583/72057594037927936)), (73/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1136927693/1152921504606846976), (-330420673/1152921504606846976)), (9/144115188075855872), by norm_num⟩
  | 16 => ⟨((63659405/576460752303423488), (296017185/9223372036854775808)), (33/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (92105944731/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444896295437075/158456325028528675187087900672), (218195603735/316912650057057350374175801344)), (23061/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945330106367561/19807040628566084398385987584), (245436547895/19807040628566084398385987584)), (51889/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945246283157611/1237940039285380274899124224), (260735218531/1237940039285380274899124224)), (55133/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886079341869513/77371252455336267181195264), (521377955491/154742504910672534362390528)), (55135/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460781621551/9671406556917033397649408), (30543349661/604462909807314587353088)), (51691/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259582480015507/604462909807314587353088), (427508682401/604462909807314587353088)), (2827/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1889081701031115/75557863725914323419136), (347258757353/37778931862957161709568)), (73505/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324626616201629/1180591620717411303424), (130181777123/1180591620717411303424)), (13783/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202847172544783/73786976294838206464), (715738207295/590295810358705651712)), (75811/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912567818614811/36893488147419103232), (894280588733/73786976294838206464)), (23693/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824524751606223/9223372036854775808), (1005526720287/9223372036854775808)), (26657/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398943066807239/288230376151711744), (502426740421/576460752303423488)), (53321/576460752303423488), by norm_num⟩
  | 5 => ⟨((598071377298819/72057594037927936), (878490003321/144115188075855872)), (93327/144115188075855872), by norm_num⟩
  | 4 => ⟨((746989081330883/18014398509481984), (1316222923755/36028797018963968)), (140019/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492179739127597/9007199254740992), (821317946061/4503599627370496)), (43769/2251799813685248), by norm_num⟩
  | 2 => ⟨((558445133038083/1125899906842624), (409669624639/562949953421312)), (350309/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112411646188125/1125899906842624), (4896295700319/2251799813685248)), (131465/562949953421312), by norm_num⟩
  | 0 => ⟨((2198055904809591/2251799813685248), (9713914618627/2251799813685248)), (1053317/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2198055904809591/2251799813685248), (9713914618627/2251799813685248)), (4018085488326262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2145552802326685/2251799813685248), (9482071743911/1125899906842624)), (516361/562949953421312), by norm_num⟩
  | 2 => ⟨((2044159148099595/2251799813685248), (9034677717961/562949953421312)), (1985385/1125899906842624), by norm_num⟩
  | 3 => ⟨((1855085248230541/2251799813685248), (65612649916963/2251799813685248)), (917087/281474976710656), by norm_num⟩
  | 4 => ⟨((763175358103539/1125899906842624), (54053232538053/1125899906842624)), (12515835/2251799813685248), by norm_num⟩
  | 5 => ⟨((1029425212217653/2251799813685248), (146556882536979/2251799813685248)), (18169109/2251799813685248), by norm_num⟩
  | 6 => ⟨((461070003390419/2251799813685248), (66999450391053/1125899906842624)), (37954613/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1255481927/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-681747485/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1646142406387953/9007199254740992), (-171466672738237/4503599627370496)), (142765097/9007199254740992), by norm_num⟩
  | 1 => ⟨((763713173/2147483648), (159100885/2147483648)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((-743058607/2147483648), (-309596027/4294967296)), (133/4294967296), by norm_num⟩
  | 3 => ⟨((481975095/2147483648), (100407675/2147483648)), (11/536870912), by norm_num⟩
  | 4 => ⟨((-937880229/8589934592), (-97692157/4294967296)), (87/8589934592), by norm_num⟩
  | 5 => ⟨((1460024525/34359738368), (594063/67108864)), (137/34359738368), by norm_num⟩
  | 6 => ⟨((-473512757/34359738368), (-98644755/34359738368)), (45/34359738368), by norm_num⟩
  | 7 => ⟨((263260937/68719476736), (109687903/137438953472)), (51/137438953472), by norm_num⟩
  | 8 => ⟨((-512282129/549755813888), (-53360701/274877906944)), (101/1099511627776), by norm_num⟩
  | 9 => ⟨((55380833/274877906944), (92297893/2199023255552)), (11/549755813888), by norm_num⟩
  | 10 => ⟨((-21553225/549755813888), (-287365451/35184372088832)), (139/35184372088832), by norm_num⟩
  | 11 => ⟨((244018265/35184372088832), (101670427/70368744177664)), (25/35184372088832), by norm_num⟩
  | 12 => ⟨((-1266233649/1125899906842624), (-16486793/70368744177664)), (33/281474976710656), by norm_num⟩
  | 13 => ⟨((758146741/4503599627370496), (157941257/4503599627370496)), (5/281474976710656), by norm_num⟩
  | 14 => ⟨((-421510125/18014398509481984), (-351245137/72057594037927936)), (45/18014398509481984), by norm_num⟩
  | 15 => ⟨((874902219/288230376151711744), (91132197/144115188075855872)), (189/576460752303423488), by norm_num⟩
  | 16 => ⟨((-425620277/1152921504606846976), (-177335067/2305843009213693952)), (93/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-1912367307981/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779369200192689/633825300114114700748351602688), (-2264667395245/316912650057057350374175801344)), (46323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890416640660971/39614081257132168796771975168), (-5094717418617/39614081257132168796771975168)), (1629/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((945116505744015/1237940039285380274899124224), (-338262924735/154742504910672534362390528)), (27701/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885949137480421/77371252455336267181195264), (-2705579945553/77371252455336267181195264)), (55421/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550215741551415/9671406556917033397649408), (-1267962514889/2417851639229258349412352)), (51977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314841790913951/151115727451828646838272), (-2218378230549/302231454903657293676544)), (11375/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888730113789223/75557863725914323419136), (-7207643604713/75557863725914323419136)), (36987/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40570040301221/147573952589676412928), (-5403907759901/4722366482869645213696)), (55513/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622410353965687/590295810358705651712), (-7427407628911/590295810358705651712)), (76383/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824673242209223/73786976294838206464), (-2319952803445/18446744073709551616)), (47779/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227999949600175/1152921504606846976), (-652104447423/576460752303423488)), (26903/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398810230277969/288230376151711744), (-2606506393769/288230376151711744)), (107749/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74729429634777/9007199254740992), (-2278542772773/36028797018963968)), (47217/72057594037927936), by norm_num⟩
  | 4 => ⟨((373314117098483/9007199254740992), (-13654054085115/36028797018963968)), (141959/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491253413456655/9007199254740992), (-2129682911489/1125899906842624)), (44497/2251799813685248), by norm_num⟩
  | 2 => ⟨((557963885222913/1125899906842624), (-8496153685111/1125899906842624)), (89399/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110877973431721/1125899906842624), (-25375574292585/1125899906842624)), (270225/1125899906842624), by norm_num⟩
  | 0 => ⟨((136950482200615/140737488355328), (-1571863396493/35184372088832)), (274297/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((136950482200615/140737488355328), (-1571863396493/35184372088832)), (1046360018016624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((132984485662641/140737488355328), (-12236537833315/140737488355328)), (1116683/1125899906842624), by norm_num⟩
  | 2 => ⟨((124594667517009/140737488355328), (-184999145182569/1125899906842624)), (576129/281474976710656), by norm_num⟩
  | 3 => ⟨((852030012229981/1125899906842624), (-40944859920261/140737488355328)), (2418845/562949953421312), by norm_num⟩
  | 4 => ⟨((274740373692095/562949953421312), (-1936575871809/4398046511104)), (10136755/1125899906842624), by norm_num⟩
  | 5 => ⟨((199476772805193/4503599627370496), (-1935606919519703/4503599627370496)), (75284733/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1646142406387953/9007199254740992), (-171466672738237/4503599627370496)), (142765097/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-681747485/16777216)), (1/33554432), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-364265031/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1270839577882493/9007199254740992), (397068696719551/4503599627370496)), (73329377/4503599627370496), by norm_num⟩
  | 1 => ⟨((-315026833/1073741824), (-196857725/1073741824)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((1310159767/4294967296), (409354131/2147483648)), (157/4294967296), by norm_num⟩
  | 3 => ⟨((-908133549/4294967296), (-141871331/1073741824)), (111/4294967296), by norm_num⟩
  | 4 => ⟨((472102657/4294967296), (590026279/8589934592)), (59/4294967296), by norm_num⟩
  | 5 => ⟨((-392683951/8589934592), (-245385031/8589934592)), (25/4294967296), by norm_num⟩
  | 6 => ⟨((544375547/34359738368), (340175885/34359738368)), (141/68719476736), by norm_num⟩
  | 7 => ⟨((-646855501/137438953472), (-404214781/137438953472)), (85/137438953472), by norm_num⟩
  | 8 => ⟨((168137275/137438953472), (52533813/68719476736)), (45/274877906944), by norm_num⟩
  | 9 => ⟨((-310783675/1099511627776), (-97103105/549755813888)), (169/4398046511104), by norm_num⟩
  | 10 => ⟨((1034010375/17592186044416), (646144737/17592186044416)), (143/17592186044416), by norm_num⟩
  | 11 => ⟨((-781877865/70368744177664), (-488589167/70368744177664)), (55/35184372088832), by norm_num⟩
  | 12 => ⟨((1083912875/562949953421312), (677328407/562949953421312)), (155/562949953421312), by norm_num⟩
  | 13 => ⟨((-173379497/562949953421312), (-433373793/2251799813685248)), (101/2251799813685248), by norm_num⟩
  | 14 => ⟨((824074351/18014398509481984), (257478705/9007199254740992)), (61/9007199254740992), by norm_num⟩
  | 15 => ⟨((-913927701/144115188075855872), (-571106043/144115188075855872)), (137/144115188075855872), by norm_num⟩
  | 16 => ⟨((475114807/576460752303423488), (593790815/1152921504606846976)), (145/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (181884184693/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779202126857275/633825300114114700748351602688), (861401341197/633825300114114700748351602688)), (92285/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118139332653211/2475880078570760549798248448), (484461852239/19807040628566084398385987584)), (51913/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472508700396901/618970019642690137449562112), (1029293082617/2475880078570760549798248448)), (55161/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442925245556953/38685626227668133590597632), (1029081248935/154742504910672534362390528)), (110329/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550031753613323/9671406556917033397649408), (482269328673/4835703278458516698824704)), (103441/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314801786914211/151115727451828646838272), (421873189439/302231454903657293676544)), (90519/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888471911830543/75557863725914323419136), (685333117091/37778931862957161709568)), (73553/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298049233031811/4722366482869645213696), (1027630890841/4722366482869645213696)), (55171/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811074432791251/295147905179352825856), (1412393467177/590295810358705651712)), (37935/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824350262061873/73786976294838206464), (1764593790379/73786976294838206464)), (189705/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911820786672187/4611686018427387904), (1983933964305/9223372036854775808)), (53365/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797444774899729/576460752303423488), (991196270651/576460752303423488)), (26689/144115188075855872), by norm_num⟩
  | 5 => ⟨((149421361881185/18014398509481984), (1732860938109/144115188075855872)), (93441/72057594037927936), by norm_num⟩
  | 4 => ⟨((373205352290111/9007199254740992), (1297915122877/18014398509481984)), (35055/4503599627370496), by norm_num⟩
  | 3 => ⟨((745367804311281/4503599627370496), (3238739561229/9007199254740992)), (87689/2251799813685248), by norm_num⟩
  | 2 => ⟨((278862212499585/562949953421312), (6459369479557/4503599627370496)), (175533/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220512597865123/2251799813685248), (4821951357651/1125899906842624)), (527377/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094744310088849/1125899906842624), (4776983300743/562949953421312)), (2115759/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094744310088849/1125899906842624), (4776983300743/562949953421312)), (8070980080611418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128739542318115/2251799813685248), (37158367319121/2251799813685248)), (4150333/2251799813685248), by norm_num⟩
  | 2 => ⟨((2011791308994277/2251799813685248), (4390959031941/140737488355328)), (7984013/2251799813685248), by norm_num⟩
  | 3 => ⟨((224396526777445/281474976710656), (125534330928315/2251799813685248)), (3691067/562949953421312), by norm_num⟩
  | 4 => ⟨((178017845490449/281474976710656), (200156107522135/2251799813685248)), (12593405/1125899906842624), by norm_num⟩
  | 5 => ⟨((220725676031987/562949953421312), (253176033189427/2251799813685248)), (18168093/1125899906842624), by norm_num⟩
  | 6 => ⟨((1270839577882493/9007199254740992), (397068696719551/4503599627370496)), (73329377/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-364265031/8388608)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile016Terms0

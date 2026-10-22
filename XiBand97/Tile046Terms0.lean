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
namespace Reinmann.XiBand97.Tile046Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨46,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36843/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36843/1280))
  have he : value ((69/80), (36843/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-669453427/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((559883579146889/2251799813685248), (-1104708154325633/2251799813685248)), (10171615/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1480414293/8589934592), (1460505185/4294967296)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((2052289987/34359738368), (-4049380205/34359738368)), (5/2147483648), by norm_num⟩
  | 3 => ⟨((-1896718691/137438953472), (3742421963/137438953472)), (75/137438953472), by norm_num⟩
  | 4 => ⟨((1314705213/549755813888), (-5188098465/1099511627776)), (53/549755813888), by norm_num⟩
  | 5 => ⟨((-1458054739/4398046511104), (2876892659/4398046511104)), (15/1099511627776), by norm_num⟩
  | 6 => ⟨((2695057417/70368744177664), (-5317626761/70368744177664)), (113/70368744177664), by norm_num⟩
  | 7 => ⟨((-133433675/35184372088832), (2106227427/281474976710656)), (23/140737488355328), by norm_num⟩
  | 8 => ⟨((739913405/2251799813685248), (-2919851205/4503599627370496)), (65/4503599627370496), by norm_num⟩
  | 9 => ⟨((-1823533833/72057594037927936), (899505169/18014398509481984)), (41/36028797018963968), by norm_num⟩
  | 10 => ⟨((252795467/144115188075855872), (-997583155/288230376151711744)), (93/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-2038975595/18446744073709551616), (4023109535/18446744073709551616)), (3/576460752303423488), by norm_num⟩
  | 12 => ⟨((471103395/73786976294838206464), (-3718142709/295147905179352825856)), (91/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-803800591/2361183241434822606848), (792990811/1180591620717411303424)), (79/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((1273490545/75557863725914323419136), (-1256364217/37778931862957161709568)), (127/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-1883128279/2417851639229258349412352), (3715606677/2417851639229258349412352)), (3/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((2610570115/77371252455336267181195264), (-5150924585/77371252455336267181195264)), (17/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-358775374375/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890523439948303/316912650057057350374175801344), (-425626831151/158456325028528675187087900672)), (11547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946152189056679/19807040628566084398385987584), (-957607907499/19807040628566084398385987584)), (12991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892239194066247/2475880078570760549798248448), (-2034792413327/2475880078570760549798248448)), (13805/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773904976338891/154742504910672534362390528), (-1017326235187/77371252455336267181195264)), (13807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552097574896541/9671406556917033397649408), (-119208624991/604462909807314587353088)), (6473/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315253579540513/151115727451828646838272), (-834386028405/302231454903657293676544)), (11329/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891407770722379/75557863725914323419136), (-2711475788695/75557863725914323419136)), (18413/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300250433335313/4722366482869645213696), (-2033362884239/4722366482869645213696)), (13813/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625174388780453/590295810358705651712), (-2795477527553/590295810358705651712)), (9499/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28564538683999/1152921504606846976), (-3493752238613/73786976294838206464)), (11877/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913945995259777/4611686018427387904), (-61400837099/144115188075855872)), (13367/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799568532118805/576460752303423488), (-3928631424283/1152921504606846976)), (13373/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199084206431043/144115188075855872), (-1718201266549/72057594037927936)), (23417/144115188075855872), by norm_num⟩
  | 4 => ⟨((749192426647867/18014398509481984), (-2576151881611/18014398509481984)), (17577/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497678508921833/9007199254740992), (-6436354394489/9007199254740992)), (43993/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122374663520811/2251799813685248), (-6430315943567/2251799813685248)), (44069/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120602374067917/1125899906842624), (-2407594026813/281474976710656)), (66291/1125899906842624), by norm_num⟩
  | 0 => ⟨((139408288761793/140737488355328), (-9600175538039/562949953421312)), (66669/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139408288761793/140737488355328), (-9600175538039/562949953421312)), (254322054149436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1104405712615283/1125899906842624), (-19019012762141/562949953421312)), (134353/562949953421312), by norm_num⟩
  | 2 => ⟨((270509189863929/281474976710656), (-37311853771647/562949953421312)), (545309/1125899906842624), by norm_num⟩
  | 3 => ⟨((1034936448617003/1125899906842624), (-143432989376743/1125899906842624)), (1120415/1125899906842624), by norm_num⟩
  | 4 => ⟨((233262393897077/281474976710656), (-263689565542945/1125899906842624)), (2345259/1125899906842624), by norm_num⟩
  | 5 => ⟨((711474722274103/1125899906842624), (-437046731635089/1125899906842624)), (1246409/281474976710656), by norm_num⟩
  | 6 => ⟨((559883579146889/2251799813685248), (-1104708154325633/2251799813685248)), (10171615/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-669453427/33554432)), (1/134217728), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-4244234311/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1709048364488533/4503599627370496), (-357278566204569/4503599627370496)), (32017987/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1790601287/4294967296), (748654601/8589934592)), (69/8589934592), by norm_num⟩
  | 2 => ⟨((983588289/4294967296), (-822481145/17179869184)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((-5763104967/68719476736), (602391929/34359738368)), (117/68719476736), by norm_num⟩
  | 4 => ⟨((3165708969/137438953472), (-82724397/17179869184)), (131/274877906944), by norm_num⟩
  | 5 => ⟨((-5564618841/1099511627776), (1163290101/1099511627776)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((4075572427/4398046511104), (-6656275/34359738368)), (11/549755813888), by norm_num⟩
  | 7 => ⟨((-19988723/137438953472), (534869249/17592186044416)), (113/35184372088832), by norm_num⟩
  | 8 => ⟨((5621723321/281474976710656), (-293806965/70368744177664)), (127/281474976710656), by norm_num⟩
  | 9 => ⟨((-5489861621/2251799813685248), (1147662017/2251799813685248)), (127/2251799813685248), by norm_num⟩
  | 10 => ⟨((2355949/8796093022208), (-252167119/4503599627370496)), (57/9007199254740992), by norm_num⟩
  | 11 => ⟨((-3855117253/144115188075855872), (201479197/36028797018963968)), (93/144115188075855872), by norm_num⟩
  | 12 => ⟨((2823519459/1152921504606846976), (-295130029/576460752303423488)), (69/1152921504606846976), by norm_num⟩
  | 13 => ⟨((-3817788523/18446744073709551616), (798113173/18446744073709551616)), (95/18446744073709551616), by norm_num⟩
  | 14 => ⟨((599181341/36893488147419103232), (-501038251/147573952589676412928)), (61/147573952589676412928), by norm_num⟩
  | 15 => ⟨((-5617220133/4722366482869645213696), (1174286463/4722366482869645213696)), (73/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((6171147067/75557863725914323419136), (-1290085539/75557863725914323419136)), (163/75557863725914323419136), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-268446469061/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890254051170069/316912650057057350374175801344), (-318283370909/633825300114114700748351602688)), (23059/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945849193054377/19807040628566084398385987584), (-358038420289/39614081257132168796771975168)), (12971/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945797744377265/1237940039285380274899124224), (-190189516443/1237940039285380274899124224)), (27563/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773261452341559/154742504910672534362390528), (-380337651695/154742504910672534362390528)), (6891/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775747231882291/4835703278458516698824704), (-356522587225/9671406556917033397649408)), (12921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260486788502261/604462909807314587353088), (-77978327411/151115727451828646838272)), (5653/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890550896039895/75557863725914323419136), (-253388364545/37778931862957161709568)), (18373/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299608093137215/4722366482869645213696), (-380010462621/4722366482869645213696)), (27561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6344889390885/2305843009213693952), (-65299659675/73786976294838206464)), (18949/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827027864228301/73786976294838206464), (-326410491443/36893488147419103232)), (47375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913326304991325/4611686018427387904), (-45886388537/576460752303423488)), (53301/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597899004926307/1152921504606846976), (-22933768749/36028797018963968)), (53305/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599001195049225/72057594037927936), (-641806370951/144115188075855872)), (5831/18014398509481984), by norm_num⟩
  | 4 => ⟨((46773909309123/1125899906842624), (-481015829937/18014398509481984)), (34991/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495659006007281/9007199254740992), (-300338545283/2251799813685248)), (10937/1125899906842624), by norm_num⟩
  | 2 => ⟨((1120362938467647/2251799813685248), (-599788969805/1125899906842624)), (175047/4503599627370496), by norm_num⟩
  | 1 => ⟨((1117604199136371/1125899906842624), (-3589865541291/2251799813685248)), (262713/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218694837839293/2251799813685248), (-7144335447009/2251799813685248)), (262999/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218694837839293/2251799813685248), (-7144335447009/2251799813685248)), (1003261570457076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1093026944937347/1125899906842624), (-14078605104891/2251799813685248)), (1039869/2251799813685248), by norm_num⟩
  | 2 => ⟨((2122139531796999/2251799813685248), (-6833775646155/562949953421312)), (508005/562949953421312), by norm_num⟩
  | 3 => ⟨((1999613356932117/2251799813685248), (-51522254729751/2251799813685248)), (3879365/2251799813685248), by norm_num⟩
  | 4 => ⟨((1774491235945815/2251799813685248), (-11438027051821/281474976710656)), (7067329/2251799813685248), by norm_num⟩
  | 5 => ⟨((348659559537763/562949953421312), (-18027072066189/281474976710656)), (5856473/1125899906842624), by norm_num⟩
  | 6 => ⟨((1709048364488533/4503599627370496), (-357278566204569/4503599627370496)), (32017987/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-4244234311/134217728)), (1/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-669453427/16777216)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-805498320519913/4503599627370496), (-1098690836721211/4503599627370496)), (30360091/2251799813685248), by norm_num⟩
  | 1 => ⟨((2129855689/8589934592), (726274925/2147483648)), (163/8589934592), by norm_num⟩
  | 2 => ⟨((-738151733/4294967296), (-4027323333/17179869184)), (57/4294967296), by norm_num⟩
  | 3 => ⟨((2728788227/34359738368), (3722037085/34359738368)), (213/34359738368), by norm_num⟩
  | 4 => ⟨((-945725933/34359738368), (-322489939/8589934592)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((2097687245/274877906944), (2861222297/274877906944)), (167/274877906944), by norm_num⟩
  | 6 => ⟨((-969337333/549755813888), (-2644330891/1099511627776)), (39/274877906944), by norm_num⟩
  | 7 => ⟨((1535756433/4398046511104), (2094754859/4398046511104)), (249/8796093022208), by norm_num⟩
  | 8 => ⟨((-2129010483/35184372088832), (-2903946849/35184372088832)), (87/17592186044416), by norm_num⟩
  | 9 => ⟨((655874495/70368744177664), (894605587/70368744177664)), (27/35184372088832), by norm_num⟩
  | 10 => ⟨((-2909552365/2251799813685248), (-1984298689/1125899906842624)), (121/1125899906842624), by norm_num⟩
  | 11 => ⟨((2933451663/18014398509481984), (2000597879/9007199254740992)), (123/9007199254740992), by norm_num⟩
  | 12 => ⟨((-338885625/18014398509481984), (-1848945039/72057594037927936)), (115/72057594037927936), by norm_num⟩
  | 13 => ⟨((578209515/288230376151711744), (3154685639/1152921504606846976)), (99/576460752303423488), by norm_num⟩
  | 14 => ⟨((-916078389/4611686018427387904), (-19523763/72057594037927936)), (159/9223372036854775808), by norm_num⟩
  | 15 => ⟨((2709235851/147573952589676412928), (1847683929/73786976294838206464)), (237/147573952589676412928), by norm_num⟩
  | 16 => ⟨((-234737399/147573952589676412928), (-640358453/295147905179352825856)), (83/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-358775374375/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780118843092679/633825300114114700748351602688), (-3401663241855/633825300114114700748351602688)), (23135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472815037381807/9903520314283042199192993792), (-3826450671551/39614081257132168796771975168)), (26031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945564730378949/1237940039285380274899124224), (-1016276553521/618970019642690137449562112)), (27665/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772794972690905/154742504910672534362390528), (-508068291667/19342813113834066795298816)), (27671/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551056659398705/9671406556917033397649408), (-3809917300933/9671406556917033397649408)), (12975/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260103230201265/604462909807314587353088), (-833270684197/151115727451828646838272)), (22713/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472481678806437/18889465931478580854784), (-5415143975279/75557863725914323419136)), (36923/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649569585862473/2361183241434822606848), (-4060381911991/4722366482869645213696)), (3463/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202955705130421/73786976294838206464), (-697679869683/73786976294838206464)), (38113/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114138649863009/4611686018427387904), (-6974419337651/73786976294838206464)), (47671/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912869666392029/4611686018427387904), (-7842949971761/9223372036854775808)), (26835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596982446990237/1152921504606846976), (-7838859998921/1152921504606846976)), (53721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197196716033103/144115188075855872), (-1713600236999/36028797018963968)), (5883/18014398509481984), by norm_num⟩
  | 4 => ⟨((1495549227441829/36028797018963968), (-2568099375589/9007199254740992)), (70711/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494126316942045/9007199254740992), (-3206097052703/2251799813685248)), (88591/9007199254740992), by norm_num⟩
  | 2 => ⟨((279702757146981/562949953421312), (-6400110836799/1125899906842624)), (88893/2251799813685248), by norm_num⟩
  | 1 => ⟨((278807119255889/281474976710656), (-19139904144599/1125899906842624)), (134099/1125899906842624), by norm_num⟩
  | 0 => ⟨((276101428153821/281474976710656), (-19019012762141/562949953421312)), (271239/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276101428153821/281474976710656), (-19019012762141/562949953421312)), (1034694675925826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((541018379727859/562949953421312), (-37311853771647/562949953421312)), (275225/562949953421312), by norm_num⟩
  | 2 => ⟨((1034936448617007/1125899906842624), (-143432989376743/1125899906842624)), (565489/562949953421312), by norm_num⟩
  | 3 => ⟨((933049575588315/1125899906842624), (-131844782771473/562949953421312)), (2367369/1125899906842624), by norm_num⟩
  | 4 => ⟨((355737361137057/562949953421312), (-218523365817547/562949953421312)), (5032639/1125899906842624), by norm_num⟩
  | 5 => ⟨((559883579146909/2251799813685248), (-1104708154325663/2251799813685248)), (20535019/2251799813685248), by norm_num⟩
  | 6 => ⟨((-805498320519913/4503599627370496), (-1098690836721211/4503599627370496)), (30360091/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-669453427/16777216)), (1/67108864), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-6217690881/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-392098849795283/2251799813685248), (-50312051013249/281474976710656)), (25276109/2251799813685248), by norm_num⟩
  | 1 => ⟨((300912263/1073741824), (2471134105/8589934592)), (157/8589934592), by norm_num⟩
  | 2 => ⟨((-3874396835/17179869184), (-3977136915/17179869184)), (255/17179869184), by norm_num⟩
  | 3 => ⟨((1039266859/8589934592), (4267303289/34359738368)), (69/8589934592), by norm_num⟩
  | 4 => ⟨((-418158871/8589934592), (-3433979849/68719476736)), (7/2147483648), by norm_num⟩
  | 5 => ⟨((2153602369/137438953472), (69084717/4294967296)), (73/68719476736), by norm_num⟩
  | 6 => ⟨((-2310726201/549755813888), (-1186000669/274877906944)), (79/274877906944), by norm_num⟩
  | 7 => ⟨((531281479/549755813888), (2181479361/2199023255552)), (147/2199023255552), by norm_num⟩
  | 8 => ⟨((-1710129109/8796093022208), (-3510955589/17592186044416)), (119/8796093022208), by norm_num⟩
  | 9 => ⟨((611632583/17592186044416), (1255703341/35184372088832)), (43/17592186044416), by norm_num⟩
  | 10 => ⟨((-393753867/70368744177664), (-1616781251/281474976710656)), (223/562949953421312), by norm_num⟩
  | 11 => ⟨((921778039/1125899906842624), (3784885879/4503599627370496)), (263/4503599627370496), by norm_num⟩
  | 12 => ⟨((-494514841/4503599627370496), (-4061025885/36028797018963968)), (285/36028797018963968), by norm_num⟩
  | 13 => ⟨((3918232287/288230376151711744), (4022134783/288230376151711744)), (285/288230376151711744), by norm_num⟩
  | 14 => ⟨((-900878799/576460752303423488), (-3699072119/2305843009213693952)), (33/288230376151711744), by norm_num⟩
  | 15 => ⟨((386642265/2305843009213693952), (1587580509/9223372036854775808)), (229/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-2489106879/147573952589676412928), (-638778065/36893488147419103232)), (93/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-3052162235301/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222477619843619/79228162514264337593543950336), (-3616167597583/633825300114114700748351602688)), (5785/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945462512126225/19807040628566084398385987584), (-4067672202201/39614081257132168796771975168)), (13019/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890773377821995/2475880078570760549798248448), (-4321287712451/2475880078570760549798248448)), (27671/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772438875941073/154742504910672534362390528), (-2160298456745/77371252455336267181195264)), (27679/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550722804069719/9671406556917033397649408), (-4049825641797/9671406556917033397649408)), (25957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314952773055011/151115727451828646838272), (-3542863482359/604462909807314587353088)), (355/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1889451963813063/75557863725914323419136), (-2877888508475/37778931862957161709568)), (36935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649391542246893/2361183241434822606848), (-2157814330525/2361183241434822606848)), (27715/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101447248928967/36893488147419103232), (-2966016393181/295147905179352825856)), (2383/36893488147419103232), by norm_num⟩
  | 8 => ⟨((912803134064413/36893488147419103232), (-3706053062297/36893488147419103232)), (11923/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825050609233775/9223372036854775808), (-8334584084367/9223372036854775808)), (839/144115188075855872), by norm_num⟩
  | 6 => ⟨((798146813669859/576460752303423488), (-8329540141807/1152921504606846976)), (53751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196593892066771/144115188075855872), (-7282673454445/144115188075855872)), (23547/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494644781295273/36028797018963968), (-2728165630375/9007199254740992)), (35381/18014398509481984), by norm_num⟩
  | 3 => ⟨((373248849733273/2251799813685248), (-6810485657519/4503599627370496)), (88667/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117679585098277/2251799813685248), (-13591189297725/2251799813685248)), (44495/1125899906842624), by norm_num⟩
  | 1 => ⟨((556765025239495/562949953421312), (-20312340689789/1125899906842624)), (33573/281474976710656), by norm_num⟩
  | 0 => ⟨((1101004127545901/1125899906842624), (-40326982691541/1125899906842624)), (16989/70368744177664), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101004127545901/1125899906842624), (-40326982691541/1125899906842624)), (64807892114138581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((67200901695547/70368744177664), (-78870553456871/1125899906842624)), (137775/281474976710656), by norm_num⟩
  | 2 => ⟨((510642861374685/562949953421312), (-75319978656247/562949953421312)), (1129793/1125899906842624), by norm_num⟩
  | 3 => ⟨((226559244865275/281474976710656), (-273286171788145/1125899906842624)), (2351957/1125899906842624), by norm_num⟩
  | 4 => ⟨((1326192722310109/2251799813685248), (-879872298930365/2251799813685248)), (1231987/281474976710656), by norm_num⟩
  | 5 => ⟨((6832117332179/35184372088832), (-1036397847012895/2251799813685248)), (1206965/140737488355328), by norm_num⟩
  | 6 => ⟨((-392098849795283/2251799813685248), (-50312051013249/281474976710656)), (25276109/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-6217690881/134217728)), (1/67108864), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-6922048019/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1950452194869/35184372088832), (-927273398859253/4503599627370496)), (8745781/1125899906842624), by norm_num⟩
  | 1 => ⟨((-426604149/4294967296), (6337932179/17179869184)), (241/17179869184), by norm_num⟩
  | 2 => ⟨((1528744047/17179869184), (-5678024999/17179869184)), (109/8589934592), by norm_num⟩
  | 3 => ⟨((-913047207/17179869184), (3391218353/17179869184)), (33/4294967296), by norm_num⟩
  | 4 => ⟨((1635960979/68719476736), (-1519061899/17179869184)), (239/68719476736), by norm_num⟩
  | 5 => ⟨((-586249715/68719476736), (4354869667/137438953472)), (173/137438953472), by norm_num⟩
  | 6 => ⟨((1400557971/549755813888), (-5201919309/549755813888)), (13/34359738368), by norm_num⟩
  | 7 => ⟨((-1433978861/2199023255552), (5326050389/2199023255552)), (215/2199023255552), by norm_num⟩
  | 8 => ⟨((1284672601/8796093022208), (-4771500609/8796093022208)), (195/8796093022208), by norm_num⟩
  | 9 => ⟨((-1023033021/35184372088832), (1899862533/17592186044416)), (157/35184372088832), by norm_num⟩
  | 10 => ⟨((733211641/140737488355328), (-2723277347/140737488355328)), (227/281474976710656), by norm_num⟩
  | 11 => ⟨((-955446473/1125899906842624), (887174177/281474976710656)), (75/562949953421312), by norm_num⟩
  | 12 => ⟨((285321711/2251799813685248), (-1059735155/2251799813685248)), (181/9007199254740992), by norm_num⟩
  | 13 => ⟨((-1258407083/72057594037927936), (1168486461/18014398509481984)), (201/72057594037927936), by norm_num⟩
  | 14 => ⟨((644217945/288230376151711744), (-4785478129/576460752303423488)), (13/36028797018963968), by norm_num⟩
  | 15 => ⟨((-1231235843/4611686018427387904), (1143256767/1152921504606846976)), (201/4611686018427387904), by norm_num⟩
  | 16 => ⟨((137879905/4611686018427387904), (-1024220569/9223372036854775808)), (91/18446744073709551616), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1703547966561/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889791553917545/316912650057057350374175801344), (-1008910657563/316912650057057350374175801344)), (23101/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890657759352863/39614081257132168796771975168), (-2269736472433/39614081257132168796771975168)), (25991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890489806822235/2475880078570760549798248448), (-1205607238975/1237940039285380274899124224)), (27619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772155752471563/154742504910672534362390528), (-1205393231943/77371252455336267181195264)), (3453/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96903615695901/604462909807314587353088), (-2259657627017/9671406556917033397649408)), (25901/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78723733344543/37778931862957161709568), (-247093229133/75557863725914323419136)), (5667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944538448154203/37778931862957161709568), (-3211359817515/75557863725914323419136)), (36843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81156410157651/295147905179352825856), (-1203887209081/2361183241434822606848)), (3455/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811385764824473/295147905179352825856), (-3309478844501/590295810358705651712)), (297/4611686018427387904), by norm_num⟩
  | 8 => ⟨((228140949614639/9223372036854775808), (-2067516364063/36893488147419103232)), (23769/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824514707831201/9223372036854775808), (-1162354025333/2305843009213693952)), (53505/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398940244268175/288230376151711744), (-4646298021209/1152921504606846976)), (53535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196131475795953/144115188075855872), (-4062005082637/144115188075855872)), (46877/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493958450282593/36028797018963968), (-190187551121/1125899906842624)), (4399/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492150221546421/9007199254740992), (-474703354639/562949953421312)), (88099/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116853458193165/2251799813685248), (-1894226330757/562949953421312)), (88279/2251799813685248), by norm_num⟩
  | 1 => ⟨((139042287145497/140737488355328), (-707473235471/70368744177664)), (265739/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197618470555095/2251799813685248), (-44913012375199/2251799813685248)), (133773/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197618470555095/2251799813685248), (-44913012375199/2251799813685248)), (510303499461936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1071922498195721/1125899906842624), (-43832344671205/1125899906842624)), (266445/562949953421312), by norm_num⟩
  | 2 => ⟨((2037652833484281/2251799813685248), (-166923813089191/2251799813685248)), (1056177/1125899906842624), by norm_num⟩
  | 3 => ⟨((1831497402817865/2251799813685248), (-75524648916401/562949953421312)), (4136111/2251799813685248), by norm_num⟩
  | 4 => ⟨((724558008041821/1125899906842624), (-491422718834825/2251799813685248)), (7837989/2251799813685248), by norm_num⟩
  | 5 => ⟨((12895524505751/35184372088832), (-158124298661669/562949953421312)), (13509125/2251799813685248), by norm_num⟩
  | 6 => ⟨((1950452194869/35184372088832), (-927273398859253/4503599627370496)), (8745781/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-6922048019/134217728)), (1/67108864), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-225263989/134217728), (-7517573493/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((180452682222225/1125899906842624), (53885916312147/562949953421312)), (20246083/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1339510749/4294967296), (-3199986311/17179869184)), (19/2147483648), by norm_num⟩
  | 2 => ⟨((2606567561/8589934592), (389180365/2147483648)), (75/8589934592), by norm_num⟩
  | 3 => ⟨((-3381430847/17179869184), (-126218337/1073741824)), (99/17179869184), by norm_num⟩
  | 4 => ⟨((1644990151/17179869184), (245609543/4294967296)), (49/17179869184), by norm_num⟩
  | 5 => ⟨((-320100303/8589934592), (-3058778255/137438953472)), (155/137438953472), by norm_num⟩
  | 6 => ⟨((3322060951/274877906944), (1984035883/274877906944)), (51/137438953472), by norm_num⟩
  | 7 => ⟨((-923490303/274877906944), (-2206146035/1099511627776)), (115/1099511627776), by norm_num⟩
  | 8 => ⟨((1797029153/2199023255552), (536620245/1099511627776)), (113/4398046511104), by norm_num⟩
  | 9 => ⟨((-3108317571/17592186044416), (-1856381833/17592186044416)), (99/17592186044416), by norm_num⟩
  | 10 => ⟨((2419402683/70368744177664), (2889881799/140737488355328)), (39/35184372088832), by norm_num⟩
  | 11 => ⟨((-3423956535/562949953421312), (-1022445513/281474976710656)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((555225981/562949953421312), (2652782801/4503599627370496)), (147/4503599627370496), by norm_num⟩
  | 13 => ⟨((-664873767/4503599627370496), (-1588331377/18014398509481984)), (89/18014398509481984), by norm_num⟩
  | 14 => ⟨((184826373/9007199254740992), (1766142941/144115188075855872)), (25/36028797018963968), by norm_num⟩
  | 15 => ⟨((-3069060395/1152921504606846976), (-1832936253/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | 16 => ⟨((2986057885/9223372036854775808), (1783364629/9223372036854775808)), (13/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532090827/10141204801825835211973625643008), (43831299509/633825300114114700748351602688)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889689899230015/316912650057057350374175801344), (830495810915/633825300114114700748351602688)), (23071/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890429173992065/39614081257132168796771975168), (116771195659/4951760157141521099596496896)), (25957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236280888538759/309485009821345068724781056), (496192607143/1237940039285380274899124224)), (6895/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771913248977795/154742504910672534362390528), (496097037459/77371252455336267181195264)), (13791/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550230711230109/9671406556917033397649408), (929978910015/9671406556917033397649408)), (6465/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314845298280207/151115727451828646838272), (813528567701/604462909807314587353088)), (22629/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944377328068507/37778931862957161709568), (660801729035/37778931862957161709568)), (36775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298261221658281/4722366482869645213696), (990869807479/4722366482869645213696)), (27585/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811220118440341/295147905179352825856), (680952716707/295147905179352825856)), (37933/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28511161041621/1152921504606846976), (1701571358407/73786976294838206464)), (741/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1824050890550453/9223372036854775808), (1913154072965/9223372036854775808)), (26681/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398824643992973/288230376151711744), (238970362719/144115188075855872)), (26687/576460752303423488), by norm_num⟩
  | 5 => ⟨((298932116446265/36028797018963968), (835614395457/72057594037927936)), (46717/144115188075855872), by norm_num⟩
  | 4 => ⟨((373339277887917/9007199254740992), (1251859492975/18014398509481984)), (8763/4503599627370496), by norm_num⟩
  | 3 => ⟨((1491404094005711/9007199254740992), (3124188789271/9007199254740992)), (87679/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116115624250535/2251799813685248), (6232027339243/4503599627370496)), (175505/4503599627370496), by norm_num⟩
  | 1 => ⟨((1111252192193059/1125899906842624), (9307268796255/2251799813685248)), (16477/140737488355328), by norm_num⟩
  | 0 => ⟨((137089885286591/140737488355328), (18452067617595/2251799813685248)), (264383/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((137089885286591/140737488355328), (18452067617595/2251799813685248)), (1008541111472701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2136437916826783/2251799813685248), (35947662027475/2251799813685248)), (519395/1125899906842624), by norm_num⟩
  | 2 => ⟨((506603063726843/562949953421312), (68212056604697/2251799813685248)), (2004311/2251799813685248), by norm_num⟩
  | 3 => ⟨((1821517933008349/2251799813685248), (122769125919747/2251799813685248)), (3728821/2251799813685248), by norm_num⟩
  | 4 => ⟨((1466762410192461/2251799813685248), (99309966686869/1125899906842624)), (6439205/2251799813685248), by norm_num⟩
  | 5 => ⟨((234472673501541/562949953421312), (505373958285/4398046511104)), (4762297/1125899906842624), by norm_num⟩
  | 6 => ⟨((180452682222225/1125899906842624), (53885916312147/562949953421312)), (20246083/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-225263989/134217728), (-7517573493/134217728)), (1/67108864), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-240721955/134217728), (-2008360281/33554432)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-1478566621583389/9007199254740992), (60996009794417/2251799813685248)), (47301235/4503599627370496), by norm_num⟩
  | 1 => ⟨((5864320479/17179869184), (-967694371/17179869184)), (189/8589934592), by norm_num⟩
  | 2 => ⟨((-6097255809/17179869184), (1006131937/17179869184)), (99/4294967296), by norm_num⟩
  | 3 => ⟨((4226295673/17179869184), (-697397515/17179869184)), (277/17179869184), by norm_num⟩
  | 4 => ⟨((-4394167395/34359738368), (362549341/17179869184)), (145/17179869184), by norm_num⟩
  | 5 => ⟨((3654965689/68719476736), (-1206240257/137438953472)), (485/137438953472), by norm_num⟩
  | 6 => ⟨((-5066858325/274877906944), (836102033/274877906944)), (169/137438953472), by norm_num⟩
  | 7 => ⟨((6020706107/1099511627776), (-248375043/274877906944)), (101/274877906944), by norm_num⟩
  | 8 => ⟨((-6259853195/4398046511104), (1032962765/4398046511104)), (423/4398046511104), by norm_num⟩
  | 9 => ⟨((5785332791/17592186044416), (-59666269/1099511627776)), (393/17592186044416), by norm_num⟩
  | 10 => ⟨((-601513067/8796093022208), (397032059/35184372088832)), (329/70368744177664), by norm_num⟩
  | 11 => ⟨((227420229/17592186044416), (-1200879937/562949953421312)), (501/562949953421312), by norm_num⟩
  | 12 => ⟨((-5044342097/2251799813685248), (832386543/2251799813685248)), (175/1125899906842624), by norm_num⟩
  | 13 => ⟨((806878039/2251799813685248), (-133146089/2251799813685248)), (451/18014398509481984), by norm_num⟩
  | 14 => ⟨((-1917549387/36028797018963968), (632844591/72057594037927936)), (135/36028797018963968), by norm_num⟩
  | 15 => ⟨((1063315161/144115188075855872), (-350923555/288230376151711744)), (151/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1105550859/1152921504606846976), (364862509/2305843009213693952)), (79/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509236873/10141204801825835211973625643008), (1939622945693/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779191241856099/633825300114114700748351602688), (1148253907891/158456325028528675187087900672)), (34745/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890216453706495/39614081257132168796771975168), (2583148086015/19807040628566084398385987584)), (39099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945010163859213/1237940039285380274899124224), (2744090821031/1237940039285380274899124224)), (41555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885842803986245/77371252455336267181195264), (1371761870237/38685626227668133590597632)), (41569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550016384117039/9671406556917033397649408), (1285725499475/2417851639229258349412352)), (38987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259192743809681/604462909807314587353088), (2249417133447/302231454903657293676544)), (2133/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((472111678801803/18889465931478580854784), (3654173208523/37778931862957161709568)), (27743/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298028770250563/4722366482869645213696), (5479283028247/4722366482869645213696)), (5205/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622118187987839/590295810358705651712), (3765401014259/295147905179352825856)), (28647/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912154053649403/36893488147419103232), (9408684579283/73786976294838206464)), (71679/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911794460135055/4611686018427387904), (10578145866941/9223372036854775808)), (80721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398707592647125/288230376151711744), (5284933063367/576460752303423488)), (80825/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195311785173727/144115188075855872), (9239319012547/144115188075855872)), (70839/144115188075855872), by norm_num⟩
  | 4 => ⟨((746359061390111/18014398509481984), (6920176504403/18014398509481984)), (106493/36028797018963968), by norm_num⟩
  | 3 => ⟨((186322623825095/1125899906842624), (17267851643371/9007199254740992)), (66763/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115256122101777/2251799813685248), (17218977528285/2251799813685248)), (67071/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109872474704515/1125899906842624), (25706318268497/1125899906842624)), (101379/562949953421312), by norm_num⟩
  | 0 => ⟨((136700122359681/140737488355328), (50924277383967/1125899906842624)), (205857/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((136700122359681/140737488355328), (50924277383967/1125899906842624)), (785282137157249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((529962659967357/562949953421312), (98926803807823/1125899906842624)), (837051/1125899906842624), by norm_num⟩
  | 2 => ⟨((989124490160153/1125899906842624), (186259939340739/1125899906842624)), (1723099/1125899906842624), by norm_num⟩
  | 3 => ⟨((419075659521869/562949953421312), (327265801192435/1125899906842624)), (3597663/1125899906842624), by norm_num⟩
  | 4 => ⟨((1057633498974709/2251799813685248), (487251595422125/1125899906842624)), (14895741/2251799813685248), by norm_num⟩
  | 5 => ⟨((37510472325555/1125899906842624), (28606761945233/70368744177664)), (26885323/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1478566621583389/9007199254740992), (60996009794417/2251799813685248)), (47301235/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-240721955/134217728), (-2008360281/33554432)), (3/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile046Terms0

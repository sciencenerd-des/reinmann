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
namespace Reinmann.XiBand97.Tile020Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27893/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27893/1280))
  have he : value ((69/80), (27893/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-803303393/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-984335993947609/9007199254740992), (58090256670961/562949953421312)), (245639019/9007199254740992), by norm_num⟩
  | 1 => ⟨((1031306857/4294967296), (-973795621/4294967296)), (65/1073741824), by norm_num⟩
  | 2 => ⟨((-566503193/2147483648), (267455959/1073741824)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((829823159/4294967296), (-391773871/2147483648)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((-28489185/268435456), (430407589/4294967296)), (239/8589934592), by norm_num⟩
  | 5 => ⟨((25038855/536870912), (-378280853/8589934592)), (213/17179869184), by norm_num⟩
  | 6 => ⟨((-586837201/34359738368), (69263999/4294967296)), (79/17179869184), by norm_num⟩
  | 7 => ⟨((368403749/68719476736), (-21741223/4294967296)), (25/17179869184), by norm_num⟩
  | 8 => ⟨((-202366443/137438953472), (95540699/68719476736)), (111/274877906944), by norm_num⟩
  | 9 => ⟨((790479151/2199023255552), (-746397767/2199023255552)), (219/2199023255552), by norm_num⟩
  | 10 => ⟨((-86843011/1099511627776), (656001407/8796093022208)), (195/8796093022208), by norm_num⟩
  | 11 => ⟨((69386763/4398046511104), (-131034765/8796093022208)), (79/17592186044416), by norm_num⟩
  | 12 => ⟨((-813110939/281474976710656), (767767483/281474976710656)), (117/140737488355328), by norm_num⟩
  | 13 => ⟨((1099438363/2251799813685248), (-8110373/17592186044416)), (319/2251799813685248), by norm_num⟩
  | 14 => ⟨((-10784433/140737488355328), (651714227/9007199254740992)), (101/4503599627370496), by norm_num⟩
  | 15 => ⟨((808817365/72057594037927936), (-763713343/72057594037927936)), (239/72057594037927936), by norm_num⟩
  | 16 => ⟨((-888576697/576460752303423488), (26219527/18014398509481984)), (265/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (776639559185/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779038623940281/633825300114114700748351602688), (114923104869/19807040628566084398385987584)), (46281/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236255627608307/4951760157141521099596496896), (4136528185921/39614081257132168796771975168)), (104155/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889838513504229/2475880078570760549798248448), (1098552429809/618970019642690137449562112)), (27673/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771504168419367/154742504910672534362390528), (4393251880475/154742504910672534362390528)), (55361/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549846682424015/9671406556917033397649408), (1029414018849/2417851639229258349412352)), (51917/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259044652503597/604462909807314587353088), (3601931661973/604462909807314587353088)), (11361/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888206812024033/75557863725914323419136), (731403956911/9444732965739290427392)), (18469/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324462373612941/1180591620717411303424), (4386755195229/4722366482869645213696)), (110867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621872741748549/590295810358705651712), (47102169051/4611686018427387904)), (9533/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1824002884992967/73786976294838206464), (1883070505951/18446744073709551616)), (190789/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823247722819943/9223372036854775808), (8468229670203/9223372036854775808)), (214815/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594491891579589/1152921504606846976), (2115311966821/288230376151711744)), (215037/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298754667329817/36028797018963968), (231116908729/4503599627370496)), (188407/144115188075855872), by norm_num⟩
  | 4 => ⟨((746142271568519/18014398509481984), (11077919331049/36028797018963968)), (141555/18014398509481984), by norm_num⟩
  | 3 => ⟨((372512413213481/2251799813685248), (13819958664849/9007199254740992)), (354763/9007199254740992), by norm_num⟩
  | 2 => ⟨((139342585463701/281474976710656), (3444710001715/562949953421312)), (356079/2251799813685248), by norm_num⟩
  | 1 => ⟨((554569435036761/562949953421312), (20565611042747/1125899906842624)), (537415/1125899906842624), by norm_num⟩
  | 0 => ⟨((136536351177503/140737488355328), (2545094696823/70368744177664)), (272015/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((136536351177503/140737488355328), (2545094696823/70368744177664)), (1037654877782726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((264553039596695/281474976710656), (79011884578319/1125899906842624)), (547467/281474976710656), by norm_num⟩
  | 2 => ⟨((247262231634735/281474976710656), (74261785092693/562949953421312)), (1105947/281474976710656), by norm_num⟩
  | 3 => ⟨((1698478741096239/2251799813685248), (521883257169929/2251799813685248)), (17878605/2251799813685248), by norm_num⟩
  | 4 => ⟨((4531909396091/8796093022208), (196822029260787/562949953421312)), (17628999/1125899906842624), by norm_num⟩
  | 5 => ⟨((322483851970771/2251799813685248), (811250723713473/2251799813685248)), (60985381/2251799813685248), by norm_num⟩
  | 6 => ⟨((-984335993947609/9007199254740992), (58090256670961/562949953421312)), (245639019/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-803303393/16777216)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66638419/33554432), (-420911553/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((307829871393587/2251799813685248), (109772529926235/9007199254740992)), (82873487/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1351937243/4294967296), (-60262821/2147483648)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((1556475271/4294967296), (138760273/4294967296)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((-1194638919/4294967296), (-106502445/4294967296)), (43/2147483648), by norm_num⟩
  | 4 => ⟨((1375378883/8589934592), (122615471/8589934592)), (101/8589934592), by norm_num⟩
  | 5 => ⟨((-1266770765/17179869184), (-56466511/8589934592)), (95/17179869184), by norm_num⟩
  | 6 => ⟨((1944564987/68719476736), (173358595/68719476736)), (149/68719476736), by norm_num⟩
  | 7 => ⟨((-1279293243/137438953472), (-114049405/137438953472)), (25/34359738368), by norm_num⟩
  | 8 => ⟨((184105097/68719476736), (65652115/274877906944)), (117/549755813888), by norm_num⟩
  | 9 => ⟨((-1507262763/2199023255552), (-134372961/2199023255552)), (61/1099511627776), by norm_num⟩
  | 10 => ⟨((347060077/2199023255552), (123762071/8796093022208)), (57/4398046511104), by norm_num⟩
  | 11 => ⟨((-1162378705/35184372088832), (-25906609/8796093022208)), (97/35184372088832), by norm_num⟩
  | 12 => ⟨((1784317253/281474976710656), (79536229/140737488355328)), (151/281474976710656), by norm_num⟩
  | 13 => ⟨((-79010429/70368744177664), (-112700883/1125899906842624)), (109/1125899906842624), by norm_num⟩
  | 14 => ⟨((6497437/35184372088832), (74143821/4503599627370496)), (73/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1021330881/36028797018963968), (-91051977/36028797018963968)), (91/36028797018963968), by norm_num⟩
  | 16 => ⟨((1175850631/288230376151711744), (52413731/144115188075855872)), (107/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (14477756795/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905729905735/633825300114114700748351602688), (68544715633/316912650057057350374175801344)), (46107/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889895953296005/39614081257132168796771975168), (77099418809/19807040628566084398385987584)), (51871/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889680693680873/2475880078570760549798248448), (40950770367/618970019642690137449562112)), (110227/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885673491598097/77371252455336267181195264), (40941440851/38685626227668133590597632)), (27557/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193712499394843/1208925819614629174706176), (38372691195/2417851639229258349412352)), (25835/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258916974599109/604462909807314587353088), (134264794309/604462909807314587353088)), (11303/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472000149310509/18889465931478580854784), (218106022871/75557863725914323419136)), (146941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297695936541029/4722366482869645213696), (163514561501/4722366482869645213696)), (110207/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810831695287885/295147905179352825856), (56181755749/147573952589676412928)), (75769/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911871939737423/36893488147419103232), (280750624355/73786976294838206464)), (189427/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227870003313445/1152921504606846976), (157813571551/4611686018427387904)), (213113/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594208794124753/1152921504606846976), (39419466973/144115188075855872)), (106561/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194776122785937/144115188075855872), (68907812643/36028797018963968)), (46623/36028797018963968), by norm_num⟩
  | 4 => ⟨((372982756477097/9007199254740992), (206418812991/18014398509481984)), (279757/36028797018963968), by norm_num⟩
  | 3 => ⟨((372406432464223/2251799813685248), (514982612615/9007199254740992)), (87433/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228687218606117/4503599627370496), (1026779023171/4503599627370496)), (699571/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217219979694883/2251799813685248), (191528459547/281474976710656)), (1049633/2251799813685248), by norm_num⟩
  | 0 => ⟨((545748820648707/562949953421312), (3032839364101/2251799813685248)), (2100405/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545748820648707/562949953421312), (3032839364101/2251799813685248)), (8012409218795012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116289013239421/2251799813685248), (183760618519/70368744177664)), (127441/70368744177664), by norm_num⟩
  | 2 => ⟨((1988917745681909/2251799813685248), (11052935009213/2251799813685248)), (1921673/562949953421312), by norm_num⟩
  | 3 => ⟨((878335544677553/1125899906842624), (19525162448357/2251799813685248)), (13654109/2251799813685248), by norm_num⟩
  | 4 => ⟨((1370242623458493/2251799813685248), (7615971939321/562949953421312)), (21540439/2251799813685248), by norm_num⟩
  | 5 => ⟨((208348538275907/562949953421312), (37075158482201/2251799813685248)), (6699493/562949953421312), by norm_num⟩
  | 6 => ⟨((307829871393587/2251799813685248), (109772529926235/9007199254740992)), (82873487/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-420911553/8388608)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-1753336849/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-230707121670635/4503599627370496), (-1040966251855911/9007199254740992)), (200996985/9007199254740992), by norm_num⟩
  | 1 => ⟨((527583615/4294967296), (74390413/268435456)), (29/536870912), by norm_num⟩
  | 2 => ⟨((-79068141/536870912), (-1427043357/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((126398081/1073741824), (1140633507/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-303089361/4294967296), (-1367559847/8589934592)), (275/8589934592), by norm_num⟩
  | 5 => ⟨((581421237/17179869184), (1311706117/17179869184)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((-464729079/34359738368), (-131055579/4294967296)), (215/34359738368), by norm_num⟩
  | 7 => ⟨((636783807/137438953472), (718302979/68719476736)), (297/137438953472), by norm_num⟩
  | 8 => ⟨((-95433805/68719476736), (-861207659/274877906944)), (45/68719476736), by norm_num⟩
  | 9 => ⟨((203413573/549755813888), (229453975/274877906944)), (97/549755813888), by norm_num⟩
  | 10 => ⟨((-97552889/1099511627776), (-880330563/4398046511104)), (47/1099511627776), by norm_num⟩
  | 11 => ⟨((340249617/17592186044416), (383807363/8796093022208)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((-543921965/140737488355328), (-613553241/70368744177664)), (67/35184372088832), by norm_num⟩
  | 13 => ⟨((401313203/562949953421312), (1768313/1099511627776)), (25/70368744177664), by norm_num⟩
  | 14 => ⟨((-549889733/4503599627370496), (-77535623/281474976710656)), (69/1125899906842624), by norm_num⟩
  | 15 => ⟨((175810399/9007199254740992), (49579281/1125899906842624)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((-421574925/144115188075855872), (-237771847/36028797018963968)), (217/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-647406968813/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889386988683521/316912650057057350374175801344), (-1532361249483/316912650057057350374175801344)), (46251/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944873736868185/19807040628566084398385987584), (-861795238507/9903520314283042199192993792)), (26021/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472380649190357/618970019642690137449562112), (-3661856125593/2475880078570760549798248448)), (27653/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771188507038177/154742504910672534362390528), (-3660985960041/154742504910672534362390528)), (110637/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549551021087481/9671406556917033397649408), (-3431249990061/9671406556917033397649408)), (103749/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258786219915033/604462909807314587353088), (-1500709811263/302231454903657293676544)), (90807/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58993355221049/2361183241434822606848), (-2437787324931/37778931862957161709568)), (36903/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297535354973427/4722366482869645213696), (-1827582883091/2361183241434822606848)), (110753/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405360380334867/147573952589676412928), (-5023391605099/590295810358705651712)), (152357/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823464940654231/73786976294838206464), (-6275549115531/73786976294838206464)), (95277/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822644020608867/9223372036854775808), (-7054921058011/9223372036854775808)), (26815/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593890043668175/1152921504606846976), (-7048585322093/1152921504606846976)), (107353/576460752303423488), by norm_num⟩
  | 5 => ⟨((597247067755549/72057594037927936), (-6160389795549/144115188075855872)), (188075/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491501901224731/36028797018963968), (-9226353322893/36028797018963968)), (141265/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489078611658061/9007199254740992), (-719254174519/562949953421312)), (353893/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113780500917771/2251799813685248), (-358462955021/70368744177664)), (177495/1125899906842624), by norm_num⟩
  | 1 => ⟨((2215451250285797/2251799813685248), (-17113301411313/1125899906842624)), (1070471/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179143473819251/2251799813685248), (-67712362995125/2251799813685248)), (2163021/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179143473819251/2251799813685248), (-67712362995125/2251799813685248)), (8251270302779387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2106795322814503/2251799813685248), (-65527562894777/1125899906842624)), (4316545/2251799813685248), by norm_num⟩
  | 2 => ⟨((490875238927363/562949953421312), (-245231680335233/2251799813685248)), (8579611/2251799813685248), by norm_num⟩
  | 3 => ⟨((1685406226151493/2251799813685248), (-213834567256861/1125899906842624)), (8415521/1125899906842624), by norm_num⟩
  | 4 => ⟨((1180252899206425/2251799813685248), (-80024456177413/281474976710656)), (31588297/2251799813685248), by norm_num⟩
  | 5 => ⟨((436604724174291/2251799813685248), (-1342202387076117/4503599627370496)), (51074585/2251799813685248), by norm_num⟩
  | 6 => ⟨((-230707121670635/4503599627370496), (-1040966251855911/9007199254740992)), (200996985/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1753336849/33554432)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-227119927/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-97281460614079/1125899906842624), (714239824698789/9007199254740992)), (48102819/2251799813685248), by norm_num⟩
  | 1 => ⟨((230536793/1073741824), (-423149893/2147483648)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((-286431205/1073741824), (525743991/2147483648)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((118625801/536870912), (-435474913/2147483648)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-589548083/4294967296), (541057253/4294967296)), (19/536870912), by norm_num⟩
  | 5 => ⟨((585988781/8589934592), (-268895353/4294967296)), (153/8589934592), by norm_num⟩
  | 6 => ⟨((-242687903/8589934592), (890906467/34359738368)), (1/134217728), by norm_num⟩
  | 7 => ⟨((689207753/68719476736), (-316259915/34359738368)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((-53519279/17179869184), (392938183/137438953472)), (231/274877906944), by norm_num⟩
  | 9 => ⟨((472854799/549755813888), (-867924181/1099511627776)), (257/1099511627776), by norm_num⟩
  | 10 => ⟨((-940000027/4398046511104), (862684227/4398046511104)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((849386297/17592186044416), (-779523553/17592186044416)), (235/17592186044416), by norm_num⟩
  | 12 => ⟨((-87943569/8796093022208), (645681087/70368744177664)), (197/70368744177664), by norm_num⟩
  | 13 => ⟨((1075847677/562949953421312), (-987358293/562949953421312)), (19/35184372088832), by norm_num⟩
  | 14 => ⟨((-190955789/562949953421312), (350499027/1125899906842624)), (109/1125899906842624), by norm_num⟩
  | 15 => ⟨((1012282261/18014398509481984), (-929021187/18014398509481984)), (291/18014398509481984), by norm_num⟩
  | 16 => ⟨((-314428365/36028797018963968), (577132731/72057594037927936)), (183/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (1562520114291/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444663999632539/158456325028528675187087900672), (1848951926559/316912650057057350374175801344)), (23141/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889614643575645/39614081257132168796771975168), (4159348162347/39614081257132168796771975168)), (52079/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236172665755937/309485009821345068724781056), (1104584888625/618970019642690137449562112)), (110695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885523540238001/77371252455336267181195264), (2208625431157/77371252455336267181195264)), (55363/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774709134113995/4835703278458516698824704), (4140016170823/9671406556917033397649408)), (51919/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78666868490825/37778931862957161709568), (905339471819/151115727451828646838272)), (90891/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887598030830903/75557863725914323419136), (735317388427/9444732965739290427392)), (147757/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648696541083995/2361183241434822606848), (4410008335895/4722366482869645213696)), (13859/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621245457056299/590295810358705651712), (6060681468841/590295810358705651712)), (152535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823219202563925/73786976294838206464), (7571233594047/73786976294838206464)), (95399/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822366662537599/9223372036854775808), (8511290551121/9223372036854775808)), (214825/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24900180620259/18014398509481984), (2125840190187/288230376151711744)), (215049/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298562299707651/36028797018963968), (7431525514639/144115188075855872)), (47105/36028797018963968), by norm_num⟩
  | 4 => ⟨((93195748647671/2251799813685248), (695592039689/2251799813685248)), (70783/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488611821106959/9007199254740992), (13880696445329/9007199254740992)), (354797/9007199254740992), by norm_num⟩
  | 2 => ⟨((139163396040227/281474976710656), (864627875245/140737488355328)), (356123/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106999405224191/1125899906842624), (20634674404829/1125899906842624)), (16797/35184372088832), by norm_num⟩
  | 0 => ⟨((1088055214561769/1125899906842624), (40805161144169/1125899906842624)), (272085/281474976710656), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088055214561769/1125899906842624), (40805161144169/1125899906842624)), (1037921906591319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((525001859212473/562949953421312), (2464598989557/35184372088832)), (545601/281474976710656), by norm_num⟩
  | 2 => ⟨((486849573353691/562949953421312), (147101565259005/1125899906842624)), (8752653/2251799813685248), by norm_num⟩
  | 3 => ⟨((1645707850523043/2251799813685248), (508864660886891/2251799813685248)), (17426025/2251799813685248), by norm_num⟩
  | 4 => ⟨((1087757033856837/2251799813685248), (371899207996097/1125899906842624)), (33347223/2251799813685248), by norm_num⟩
  | 5 => ⟨((279767001153409/2251799813685248), (1437200507522865/4503599627370496)), (27123765/1125899906842624), by norm_num⟩
  | 6 => ⟨((-97281460614079/1125899906842624), (714239824698789/9007199254740992)), (48102819/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-227119927/4194304)), (1/16777216), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-579933/262144), (-1875486505/33554432)), (3/33554432), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((390971407256665/4503599627370496), (600398300702083/9007199254740992)), (9713521/562949953421312), by norm_num⟩
  | 1 => ⟨((-239091363/1073741824), (-734325045/4294967296)), (3/67108864), by norm_num⟩
  | 2 => ⟨((306628619/1073741824), (235438319/1073741824)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((-1048649173/4294967296), (-402591577/2147483648)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((336216503/2147483648), (516313503/4294967296)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((-689902643/8589934592), (-529727195/8589934592)), (73/4294967296), by norm_num⟩
  | 6 => ⟨((1179710227/34359738368), (905815619/34359738368)), (63/8589934592), by norm_num⟩
  | 7 => ⟨((-864541997/68719476736), (-165955085/17179869184)), (93/34359738368), by norm_num⟩
  | 8 => ⟨((277188305/68719476736), (851332777/274877906944)), (241/274877906944), by norm_num⟩
  | 9 => ⟨((-315988429/274877906944), (-242625051/274877906944)), (139/549755813888), by norm_num⟩
  | 10 => ⟨((324197727/1099511627776), (497856775/2199023255552)), (9/137438953472), by norm_num⟩
  | 11 => ⟨((-604764183/8796093022208), (-14511107/274877906944)), (271/17592186044416), by norm_num⟩
  | 12 => ⟨((1034126335/70368744177664), (397016049/35184372088832)), (117/35184372088832), by norm_num⟩
  | 13 => ⟨((-816148209/281474976710656), (-626662191/281474976710656)), (187/281474976710656), by norm_num⟩
  | 14 => ⟨((1196216471/2251799813685248), (918489591/2251799813685248)), (69/562949953421312), by norm_num⟩
  | 15 => ⟨((-102274489/1125899906842624), (-157058619/2251799813685248)), (191/9007199254740992), by norm_num⟩
  | 16 => ⟨((262328885/18014398509481984), (100711851/9007199254740992)), (247/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (426484373827/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444639091823341/158456325028528675187087900672), (1009214848439/633825300114114700748351602688)), (138449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889502962183659/39614081257132168796771975168), (567573976475/19807040628566084398385987584)), (155765/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889263190546553/2475880078570760549798248448), (602911290913/1237940039285380274899124224)), (20689/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110683096014201/9671406556917033397649408), (1205516568957/154742504910672534362390528)), (41381/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549308698298619/9671406556917033397649408), (564923375747/4835703278458516698824704)), (19399/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157321831189641/75557863725914323419136), (494145497899/302231454903657293676544)), (67903/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887444430860571/75557863725914323419136), (401340978455/18889465931478580854784)), (110355/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297278909641395/4722366482869645213696), (601745177691/2361183241434822606848)), (165555/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621090137643565/590295810358705651712), (1653934274185/590295810358705651712)), (227673/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823027551872955/73786976294838206464), (2066121232029/73786976294838206464)), (71161/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911077242974665/4611686018427387904), (2322604903841/9223372036854775808)), (320299/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593403663512551/1152921504606846976), (2320380085693/1152921504606846976)), (160195/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194072094625421/144115188075855872), (2027832449377/144115188075855872)), (280445/144115188075855872), by norm_num⟩
  | 4 => ⟨((745437952878217/18014398509481984), (3036755401647/36028797018963968)), (420875/36028797018963968), by norm_num⟩
  | 3 => ⟨((372077110738931/2251799813685248), (1893610852477/4503599627370496)), (526457/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226057483187075/4503599627370496), (1887084593513/1125899906842624)), (527005/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213287467260547/2251799813685248), (11257463582659/2251799813685248)), (791883/1125899906842624), by norm_num⟩
  | 0 => ⟨((543794647083667/562949953421312), (11128029432379/1125899906842624)), (794651/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543794647083667/562949953421312), (11128029432379/1125899906842624)), (3031352998973655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2100944555657861/2251799813685248), (42997519059307/2251799813685248)), (6203727/2251799813685248), by norm_num⟩
  | 2 => ⟨((489843636686599/562949953421312), (80233955989725/2251799813685248)), (11813157/2251799813685248), by norm_num⟩
  | 3 => ⟨((851032827929617/1125899906842624), (139629082652559/2251799813685248)), (5349991/562949953421312), by norm_num⟩
  | 4 => ⟨((1277880564091451/2251799813685248), (211082587979351/2251799813685248)), (8751267/562949953421312), by norm_num⟩
  | 5 => ⟨((1410802920828957/4503599627370496), (479151539062415/4503599627370496)), (2893311/140737488355328), by norm_num⟩
  | 6 => ⟨((390971407256665/4503599627370496), (600398300702083/9007199254740992)), (9713521/562949953421312), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1875486505/33554432)), (3/33554432), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-1929674125/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((530321504339561/9007199254740992), (-757654157202123/9007199254740992)), (116327599/9007199254740992), by norm_num⟩
  | 1 => ⟨((-333678449/2147483648), (238358111/1073741824)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((220149139/1073741824), (-1258081439/4294967296)), (199/4294967296), by norm_num⟩
  | 3 => ⟨((-774648265/4294967296), (1106716347/4294967296)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((511085295/4294967296), (-182542993/1073741824)), (119/4294967296), by norm_num⟩
  | 5 => ⟨((-539513357/8589934592), (385393139/4294967296)), (1/67108864), by norm_num⟩
  | 6 => ⟨((237301113/8589934592), (-678049725/17179869184)), (115/17179869184), by norm_num⟩
  | 7 => ⟨((-89464463/8589934592), (511260599/34359738368)), (11/4294967296), by norm_num⟩
  | 8 => ⟨((236101847/68719476736), (-674623015/137438953472)), (59/68719476736), by norm_num⟩
  | 9 => ⟨((-276927249/274877906944), (197818757/137438953472)), (141/549755813888), by norm_num⟩
  | 10 => ⟨((584661509/2199023255552), (-835288065/2199023255552)), (151/2199023255552), by norm_num⟩
  | 11 => ⟨((-561074633/8796093022208), (400795107/4398046511104)), (147/8796093022208), by norm_num⟩
  | 12 => ⟨((246784687/17592186044416), (-352573755/17592186044416)), (131/35184372088832), by norm_num⟩
  | 13 => ⟨((-200393519/70368744177664), (1145184433/281474976710656)), (215/281474976710656), by norm_num⟩
  | 14 => ⟨((604399983/1125899906842624), (-215871955/281474976710656)), (41/281474976710656), by norm_num⟩
  | 15 => ⟨((-850691309/9007199254740992), (1215356725/9007199254740992)), (233/9007199254740992), by norm_num⟩
  | 16 => ⟨((561255783/36028797018963968), (-400924509/18014398509481984)), (39/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-1250640847919/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444614308317575/158456325028528675187087900672), (-184947007609/79228162514264337593543950336)), (46173/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889391423104489/39614081257132168796771975168), (-832096505359/19807040628566084398385987584)), (103899/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236143082648113/309485009821345068724781056), (-883897278167/1237940039285380274899124224)), (27601/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770810985427661/154742504910672534362390528), (-883666451385/77371252455336267181195264)), (6901/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549197534174477/9671406556917033397649408), (-1656384250083/9671406556917033397649408)), (12941/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258477358190717/604462909807314587353088), (-1448846053315/604462909807314587353088)), (11325/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887286289926769/75557863725914323419136), (-2353456160265/75557863725914323419136)), (9203/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297160266796115/4722366482869645213696), (-882144331075/2361183241434822606848)), (55229/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620926943497061/590295810358705651712), (-2424592010339/590295810358705651712)), (75957/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822823469059171/73786976294838206464), (-3028783920619/73786976294838206464)), (23743/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821924769212367/9223372036854775808), (-851173581607/2305843009213693952)), (213759/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593173792847745/1152921504606846976), (-425167238453/144115188075855872)), (26731/144115188075855872), by norm_num⟩
  | 5 => ⟨((149233848170153/18014398509481984), (-743099725915/36028797018963968)), (187219/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490573598832025/36028797018963968), (-4451065326703/36028797018963968)), (281029/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487929963123101/9007199254740992), (-5550672455393/9007199254740992)), (351641/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225298751424609/4503599627370496), (-2765490382115/1125899906842624)), (176087/1125899906842624), by norm_num⟩
  | 1 => ⟨((553036249162439/562949953421312), (-8247406448999/1125899906842624)), (264799/562949953421312), by norm_num⟩
  | 0 => ⟨((1086438248479641/1125899906842624), (-16299538369361/1125899906842624)), (2129143/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086438248479641/1125899906842624), (-16299538369361/1125899906842624)), (8122035988814543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1048123714760557/1125899906842624), (-62913023828895/2251799813685248)), (4170685/2251799813685248), by norm_num⟩
  | 2 => ⟨((1949682742899565/2251799813685248), (-58567046539047/1125899906842624)), (3999103/1125899906842624), by norm_num⟩
  | 3 => ⟨((841003356333113/1125899906842624), (-202837142530711/2251799813685248)), (14682325/2251799813685248), by norm_num⟩
  | 4 => ⟨((309530587279585/562949953421312), (-151511441310733/1125899906842624)), (24579353/2251799813685248), by norm_num⟩
  | 5 => ⟨((1279975311513665/4503599627370496), (-41653281187315/281474976710656)), (67289025/4503599627370496), by norm_num⟩
  | 6 => ⟨((530321504339561/9007199254740992), (-757654157202123/9007199254740992)), (116327599/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1929674125/33554432)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-1980121593/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42415016562271/562949953421312), (-273295916600299/4503599627370496)), (159035899/9007199254740992), by norm_num⟩
  | 1 => ⟨((438163735/2147483648), (705813467/4294967296)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-1186569391/4294967296), (-477844575/2147483648)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((267774123/1073741824), (862684731/4294967296)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-90643221/536870912), (-292024195/2147483648)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((785492457/8589934592), (39540809/536870912)), (193/8589934592), by norm_num⟩
  | 6 => ⟨((-354525501/8589934592), (-571085311/17179869184)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((1097226119/68719476736), (883730109/68719476736)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((-742835853/137438953472), (-598296375/137438953472)), (187/137438953472), by norm_num⟩
  | 9 => ⟨((894060791/549755813888), (720096275/549755813888)), (227/549755813888), by norm_num⟩
  | 10 => ⟨((-484232301/1099511627776), (-780022745/2199023255552)), (31/274877906944), by norm_num⟩
  | 11 => ⟨((953691185/8796093022208), (384061955/4398046511104)), (247/8796093022208), by norm_num⟩
  | 12 => ⟨((-430440601/17592186044416), (-693372703/35184372088832)), (225/35184372088832), by norm_num⟩
  | 13 => ⟨((179331501/35184372088832), (577750181/140737488355328)), (189/140737488355328), by norm_num⟩
  | 14 => ⟨((-1110031331/1125899906842624), (-894043711/1125899906842624)), (295/1125899906842624), by norm_num⟩
  | 15 => ⟨((801605485/4503599627370496), (322815367/2251799813685248)), (215/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1085393947/36028797018963968), (-874200219/36028797018963968)), (147/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-3209054554909/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778358987098519/633825300114114700748351602688), (-29657131991/4951760157141521099596496896)), (46287/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944640276287073/19807040628566084398385987584), (-4269743558637/39614081257132168796771975168)), (52085/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472256601626899/618970019642690137449562112), (-4535519970245/2475880078570760549798248448)), (27677/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770692219660991/154742504910672534362390528), (-4534302319051/154742504910672534362390528)), (27685/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549085648638455/9671406556917033397649408), (-1062403740707/2417851639229258349412352)), (103851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258378916169977/604462909807314587353088), (-1858559980279/302231454903657293676544)), (11363/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943562653011947/37778931862957161709568), (-6037896013521/75557863725914323419136)), (147781/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297038641163739/4722366482869645213696), (-4526301778073/4722366482869645213696)), (55445/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405189566883293/147573952589676412928), (-3110110440203/295147905179352825856)), (76281/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911305233087719/36893488147419103232), (-7770112301265/73786976294838206464)), (47709/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455420544732525/2305843009213693952), (-8734279848755/9223372036854775808)), (107437/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592927507680479/1152921504606846976), (-4362707418781/576460752303423488)), (215103/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193651139616315/144115188075855872), (-953096568587/18014398509481984)), (94237/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490235864030821/36028797018963968), (-11417247217221/36028797018963968)), (70807/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487493387777031/9007199254740992), (-7118378531379/4503599627370496)), (177471/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112191307766051/2251799813685248), (-1773080106737/281474976710656)), (22269/140737488355328), by norm_num⟩
  | 1 => ⟨((1105332075445593/1125899906842624), (-10573487213905/562949953421312)), (268935/562949953421312), by norm_num⟩
  | 0 => ⟨((1084746571799209/1125899906842624), (-10443956091747/281474976710656)), (544725/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084746571799209/1125899906842624), (-10443956091747/281474976710656)), (2077960970165061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1043547386750805/1125899906842624), (-40248855152015/562949953421312)), (2180105/1125899906842624), by norm_num⟩
  | 2 => ⟨((961463146458501/1125899906842624), (-298439229692327/2251799813685248)), (8706055/2251799813685248), by norm_num⟩
  | 3 => ⟨((400632810723353/562949953421312), (-509704848650891/2251799813685248)), (17176777/2251799813685248), by norm_num⟩
  | 4 => ⟨((1025094387912551/2251799813685248), (-181370017808227/562949953421312)), (32224365/2251799813685248), by norm_num⟩
  | 5 => ⟨((232923533959851/2251799813685248), (-165131364041227/562949953421312)), (100206335/4503599627370496), by norm_num⟩
  | 6 => ⟨((-42415016562271/562949953421312), (-273295916600299/4503599627370496)), (159035899/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1980121593/33554432)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile020Terms1

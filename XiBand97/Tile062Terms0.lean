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
namespace Reinmann.XiBand97.Tile062Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨62,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80309/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80309/2560))
  have he : value ((69/80), (80309/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/4294967296), (-93391978315/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-600504916807455/1125899906842624), (-302365859501435/2251799813685248)), (1630973/2251799813685248), by norm_num⟩
  | 1 => ⟨((101620676269/274877906944), (25583989625/274877906944)), (35/68719476736), by norm_num⟩
  | 2 => ⟨((-35219042621/274877906944), (-4433367569/137438953472)), (99/549755813888), by norm_num⟩
  | 3 => ⟨((32549306793/1099511627776), (4097301641/549755813888)), (93/2199023255552), by norm_num⟩
  | 4 => ⟨((-90245840931/17592186044416), (-22720264643/17592186044416)), (131/17592186044416), by norm_num⟩
  | 5 => ⟨((100085840317/140737488355328), (12598789903/70368744177664)), (37/35184372088832), by norm_num⟩
  | 6 => ⟨((-92498957373/1125899906842624), (-23287508533/1125899906842624)), (139/1125899906842624), by norm_num⟩
  | 7 => ⟨((2289835411/281474976710656), (18447623865/9007199254740992)), (7/562949953421312), by norm_num⟩
  | 8 => ⟨((-101580349381/144115188075855872), (-6393459235/36028797018963968)), (157/144115188075855872), by norm_num⟩
  | 9 => ⟨((3911674043/72057594037927936), (3939207327/288230376151711744)), (99/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-69410965355/18446744073709551616), (-17474882895/18446744073709551616)), (111/18446744073709551616), by norm_num⟩
  | 11 => ⟨((34990556317/147573952589676412928), (17618422995/295147905179352825856)), (57/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-64676281219/4722366482869645213696), (-4070720075/1180591620717411303424)), (107/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((27587804293/37778931862957161709568), (6945496967/37778931862957161709568)), (93/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-5463545361/151115727451828646838272), (-11004003749/1208925819614629174706176)), (149/2417851639229258349412352), by norm_num⟩
  | 15 => ⟨((4039510467/2417851639229258349412352), (16271774237/38685626227668133590597632)), (7/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-89599209313/1237940039285380274899124224), (-11278734435/618970019642690137449562112)), (157/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-942751668049/2535301200456458802993406410752)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((890518881433539/316912650057057350374175801344), (-279604199239/39614081257132168796771975168)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892293567608961/39614081257132168796771975168), (-2516287050133/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892227033311419/2475880078570760549798248448), (-5346779960811/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773892056729719/154742504910672534362390528), (-5346408419125/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552084656630047/9671406556917033397649408), (-1252965721877/2417851639229258349412352)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261002208714427/604462909807314587353088), (-2192492374353/302231454903657293676544)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((945693291022423/37778931862957161709568), (-1781214622987/18889465931478580854784)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650116610106801/2361183241434822606848), (-5342994281411/4722366482869645213696)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625148573788665/590295810358705651712), (-1836390118291/147573952589676412928)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828094987790163/73786976294838206464), (-4590181849953/36893488147419103232)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827847641988687/9223372036854775808), (-10325724107823/9223372036854775808)), (841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799543593950637/576460752303423488), (-10322988175285/1152921504606846976)), (421/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199034349818661/144115188075855872), (-4514765195305/72057594037927936)), (1477/144115188075855872), by norm_num⟩
  | 4 => ⟨((749148824332781/18014398509481984), (-13538111231865/36028797018963968)), (2219/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497547791015549/9007199254740992), (-16911780855963/9007199254740992)), (2781/9007199254740992), by norm_num⟩
  | 2 => ⟨((140276427788247/281474976710656), (-4223855644119/562949953421312)), (2793/2251799813685248), by norm_num⟩
  | 1 => ⟨((140034545192103/140737488355328), (-25301990215843/1125899906842624)), (4221/1125899906842624), by norm_num⟩
  | 0 => ⟨((139286328964807/140737488355328), (-50437922645093/1125899906842624)), (4283/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139286328964807/140737488355328), (-50437922645093/1125899906842624)), (16338350536155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((137567693669323/140737488355328), (-24958925897941/281474976710656)), (4431/281474976710656), by norm_num⟩
  | 2 => ⟨((1066901708441149/1125899906842624), (-12198391176253/70368744177664)), (18897/562949953421312), by norm_num⟩
  | 3 => ⟨((977161697485129/1125899906842624), (-184946946805237/562949953421312)), (84731/1125899906842624), by norm_num⟩
  | 4 => ⟨((363275405535691/562949953421312), (-642057331691949/1125899906842624)), (101375/562949953421312), by norm_num⟩
  | 5 => ⟨((205415176227137/2251799813685248), (-414323930804195/562949953421312)), (985827/2251799813685248), by norm_num⟩
  | 6 => ⟨((-600504916807455/1125899906842624), (-302365859501435/2251799813685248)), (1630973/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-93391978315/4294967296)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1017427393/1073741824), (-74011391749/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-1738403327097375/4503599627370496), (-162628880241503/4503599627370496)), (1111065/1125899906842624), by norm_num⟩
  | 1 => ⟨((7285428077/17179869184), (10904912495/274877906944)), (301/274877906944), by norm_num⟩
  | 2 => ⟨((-64030886509/274877906944), (-5990135437/274877906944)), (167/274877906944), by norm_num⟩
  | 3 => ⟨((93793491697/1099511627776), (1096806067/137438953472)), (247/1099511627776), by norm_num⟩
  | 4 => ⟨((-103042682575/4398046511104), (-2409929247/1099511627776)), (137/2199023255552), by norm_num⟩
  | 5 => ⟨((90563165867/17592186044416), (4236124617/8796093022208)), (243/17592186044416), by norm_num⟩
  | 6 => ⟨((-66329204615/70368744177664), (-6205144747/70368744177664)), (45/17592186044416), by norm_num⟩
  | 7 => ⟨((41640045307/281474976710656), (7790912311/562949953421312)), (57/140737488355328), by norm_num⟩
  | 8 => ⟨((-45746265475/2251799813685248), (-8559192005/4503599627370496)), (253/4503599627370496), by norm_num⟩
  | 9 => ⟨((22336626405/9007199254740992), (4179214897/18014398509481984)), (125/18014398509481984), by norm_num⟩
  | 10 => ⟨((-78525735219/288230376151711744), (-7346138949/288230376151711744)), (111/144115188075855872), by norm_num⟩
  | 11 => ⟨((125482673001/4611686018427387904), (1467374277/576460752303423488)), (357/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-22976134429/9223372036854775808), (-8597735535/36893488147419103232)), (33/4611686018427387904), by norm_num⟩
  | 13 => ⟨((124267636331/590295810358705651712), (11625326663/590295810358705651712)), (45/73786976294838206464), by norm_num⟩
  | 14 => ⟨((-19503136051/1180591620717411303424), (-7298129561/4722366482869645213696)), (57/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((45709621191/37778931862957161709568), (133630247/1180591620717411303424)), (269/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((-50217151551/604462909807314587353088), (-9395701215/1208925819614629174706176)), (149/604462909807314587353088), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (-992692144327/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890248167954105/316912650057057350374175801344), (-4707939025257/633825300114114700748351602688)), (1449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945842223067473/19807040628566084398385987584), (-1323986781067/9903520314283042199192993792)), (815/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891579808369895/2475880078570760549798248448), (-351649712833/154742504910672534362390528)), (1733/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773244794362421/154742504910672534362390528), (-5625778133847/154742504910672534362390528)), (1733/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387869452129843/2417851639229258349412352), (-5273510920449/9671406556917033397649408)), (813/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630235588557531/302231454903657293676544), (-4613665717837/604462909807314587353088)), (1423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890523581923547/75557863725914323419136), (-3747987805871/37778931862957161709568)), (1157/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299585905866665/4722366482869645213696), (-5620903880165/4722366482869645213696)), (217/590295810358705651712), by norm_num⟩
  | 9 => ⟨((406064603174583/147573952589676412928), (-1931747585057/147573952589676412928)), (2389/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826982131599109/73786976294838206464), (-9656107393695/73786976294838206464)), (747/18446744073709551616), by norm_num⟩
  | 7 => ⟨((57081108357985/288230376151711744), (-2714875233343/2305843009213693952)), (3365/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798917375787475/576460752303423488), (-5427485864365/576460752303423488)), (3369/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74871136046983/9007199254740992), (-9492998938025/144115188075855872)), (2953/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496652814586951/36028797018963968), (-7114640432833/18014398509481984)), (555/4503599627370496), by norm_num⟩
  | 3 => ⟨((93468172578529/562949953421312), (-17768686963543/9007199254740992)), (5567/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120152948121903/2251799813685248), (-17741749158931/2251799813685248)), (5593/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117185166142813/1125899906842624), (-26545047002793/1125899906842624)), (8455/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108095064818657/1125899906842624), (-52818401477567/1125899906842624)), (17173/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108095064818657/1125899906842624), (-52818401477567/1125899906842624)), (65509800437545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1088093960835595/1125899906842624), (-6497892225277/70368744177664)), (35415/1125899906842624), by norm_num⟩
  | 2 => ⟨((520978585225079/562949953421312), (-50237625888517/281474976710656)), (74993/1125899906842624), by norm_num⟩
  | 3 => ⟨((116050906681527/140737488355328), (-371936824599095/1125899906842624)), (82787/562949953421312), by norm_num⟩
  | 4 => ⟨((321344296403327/562949953421312), (-76673966239179/140737488355328)), (47807/140737488355328), by norm_num⟩
  | 5 => ⟨((65368533692841/2251799813685248), (-175068789570655/281474976710656)), (426677/562949953421312), by norm_num⟩
  | 6 => ⟨((-1738403327097375/4503599627370496), (-162628880241503/4503599627370496)), (1111065/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-74011391749/2147483648)), (1/1073741824), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-2567700857/2147483648), (-93391978315/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1199928607540471/4503599627370496), (645073986423977/4503599627370496)), (15395/35184372088832), by norm_num⟩
  | 1 => ⟨((-50764595409/137438953472), (-1705670223/8589934592)), (85/137438953472), by norm_num⟩
  | 2 => ⟨((8796834045/34359738368), (37832976193/274877906944)), (15/34359738368), by norm_num⟩
  | 3 => ⟨((-65040007639/549755813888), (-17482547187/274877906944)), (113/549755813888), by norm_num⟩
  | 4 => ⟨((22541148959/549755813888), (24235956583/1099511627776)), (5/68719476736), by norm_num⟩
  | 5 => ⟨((-6249733539/549755813888), (-13439267979/2199023255552)), (45/2199023255552), by norm_num⟩
  | 6 => ⟨((46207841939/17592186044416), (24841041889/17592186044416)), (85/17592186044416), by norm_num⟩
  | 7 => ⟨((-9151095817/17592186044416), (-19678283597/70368744177664)), (137/140737488355328), by norm_num⟩
  | 8 => ⟨((50744450117/562949953421312), (27279893587/562949953421312)), (97/562949953421312), by norm_num⟩
  | 9 => ⟨((-62530440049/4503599627370496), (-33615966801/4503599627370496)), (121/4503599627370496), by norm_num⟩
  | 10 => ⟨((34674238575/18014398509481984), (2330081261/2251799813685248)), (17/4503599627370496), by norm_num⟩
  | 11 => ⟨((-34959055573/144115188075855872), (-9396882947/72057594037927936)), (35/72057594037927936), by norm_num⟩
  | 12 => ⟨((64618055481/2305843009213693952), (34738255577/2305843009213693952)), (131/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-55125935963/18446744073709551616), (-29635352505/18446744073709551616)), (57/9223372036854775808), by norm_num⟩
  | 14 => ⟨((87338027631/295147905179352825856), (46952368077/295147905179352825856)), (183/295147905179352825856), by norm_num⟩
  | 15 => ⟨((-8071747681/295147905179352825856), (-34714561657/2361183241434822606848)), (69/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((22379636589/9444732965739290427392), (24062300537/18889465931478580854784)), (97/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (642537039493/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27814448587905/9903520314283042199192993792), (761512211015/633825300114114700748351602688)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891267095484891/39614081257132168796771975168), (428304966863/19807040628566084398385987584)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891137273694991/2475880078570760549798248448), (227509248525/618970019642690137449562112)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772803272413483/154742504910672534362390528), (909912073609/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551064957407943/9671406556917033397649408), (26653433247/302231454903657293676544)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260111007764733/604462909807314587353088), (373081725795/302231454903657293676544)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889940322321931/75557863725914323419136), (1212266889869/75557863725914323419136)), (2299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299150224078713/4722366482869645213696), (908982593063/4722366482869645213696)), (1725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623662213604227/590295810358705651712), (1249497609803/590295810358705651712)), (593/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826241175380239/73786976294838206464), (195167751041/9223372036854775808)), (2965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456441947550919/2305843009213693952), (1755781295659/9223372036854775808)), (417/1152921504606846976), by norm_num⟩
  | 6 => ⟨((798507220796117/576460752303423488), (1754871153367/1152921504606846976)), (417/144115188075855872), by norm_num⟩
  | 5 => ⟨((1197228685648633/144115188075855872), (191811118771/18014398509481984)), (365/18014398509481984), by norm_num⟩
  | 4 => ⟨((1495605118069485/36028797018963968), (2299688308923/36028797018963968)), (4381/36028797018963968), by norm_num⟩
  | 3 => ⟨((747105020267043/4503599627370496), (1435517404501/4503599627370496)), (5479/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237830973154613/4503599627370496), (5731356379905/4503599627370496)), (5483/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230873607883851/2251799813685248), (8570298645927/2251799813685248)), (16469/2251799813685248), by norm_num⟩
  | 0 => ⟨((276256937788673/281474976710656), (8516968090505/1125899906842624)), (129/8796093022208), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276256937788673/281474976710656), (8516968090505/1125899906842624)), (492095980820057/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((2168956200557199/2251799813685248), (33436315390059/2251799813685248)), (16331/562949953421312), by norm_num⟩
  | 2 => ⟨((1044331957078239/1125899906842624), (64412389723371/2251799813685248)), (127783/2251799813685248), by norm_num⟩
  | 3 => ⟨((241938024633769/281474976710656), (59745912235249/1125899906842624)), (122181/1125899906842624), by norm_num⟩
  | 4 => ⟨((414323930804193/562949953421312), (102707588113579/1125899906842624)), (446011/2251799813685248), by norm_num⟩
  | 5 => ⟨((600504916807447/1125899906842624), (37795732437683/281474976710656)), (368945/1125899906842624), by norm_num⟩
  | 6 => ⟨((1199928607540471/4503599627370496), (645073986423977/4503599627370496)), (15395/35184372088832), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-93391978315/2147483648)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-745252095/536870912), (-13553091143/268435456)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1095817531413753/4503599627370496), (-3895717323379/70368744177664)), (1317107/4503599627370496), by norm_num⟩
  | 1 => ⟨((-107644670421/274877906944), (1530741005/17179869184)), (33/68719476736), by norm_num⟩
  | 2 => ⟨((10827963353/34359738368), (-19709060861/274877906944)), (27/68719476736), by norm_num⟩
  | 3 => ⟨((-92943651919/549755813888), (1321687907/34359738368)), (59/274877906944), by norm_num⟩
  | 4 => ⟨((2337297455/34359738368), (-1063587313/68719476736)), (97/1099511627776), by norm_num⟩
  | 5 => ⟨((-24075104875/1099511627776), (21910755133/4398046511104)), (127/4398046511104), by norm_num⟩
  | 6 => ⟨((103326364085/17592186044416), (-11754666667/8796093022208)), (69/8796093022208), by norm_num⟩
  | 7 => ⟨((-95027067265/70368744177664), (21621035637/70368744177664)), (129/70368744177664), by norm_num⟩
  | 8 => ⟨((38235041191/140737488355328), (-8699428615/140737488355328)), (53/140737488355328), by norm_num⟩
  | 9 => ⟨((-54699488779/1125899906842624), (24891004853/2251799813685248)), (77/1125899906842624), by norm_num⟩
  | 10 => ⟨((35214172413/4503599627370496), (-4006052689/2251799813685248)), (101/9007199254740992), by norm_num⟩
  | 11 => ⟨((-10304549843/9007199254740992), (2344542937/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | 12 => ⟨((88450843669/576460752303423488), (-10062390107/288230376151711744)), (65/288230376151711744), by norm_num⟩
  | 13 => ⟨((-87603779193/4611686018427387904), (9966025925/2305843009213693952)), (131/4611686018427387904), by norm_num⟩
  | 14 => ⟨((40283669573/18446744073709551616), (-18331085669/36893488147419103232)), (123/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-69156336067/295147905179352825856), (7867398467/147573952589676412928)), (107/295147905179352825856), by norm_num⟩
  | 16 => ⟨((3478213411/147573952589676412928), (-12662089365/2361183241434822606848)), (87/2361183241434822606848), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (-145707854291/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827879022339/633825300114114700748351602688), (-345266064371/633825300114114700748351602688)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472733303483361/9903520314283042199192993792), (-388376534485/39614081257132168796771975168)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890782589493683/2475880078570760549798248448), (-412591624685/2475880078570760549798248448)), (431/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772448661258295/154742504910672534362390528), (-412525891177/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96920786690173/604462909807314587353088), (-386673195833/9671406556917033397649408)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((78738766329187/37778931862957161709568), (-42283654469/75557863725914323419136)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944734002332767/37778931862957161709568), (-274778324183/37778931862957161709568)), (2297/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324699028254723/1180591620717411303424), (-412053019145/4722366482869645213696)), (431/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811587758742401/295147905179352825856), (-566386958095/590295810358705651712)), (1185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57051034842697/2305843009213693952), (-707704897975/73786976294838206464)), (1481/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825084147886317/9223372036854775808), (-397892423913/4611686018427387904)), (833/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399082832744701/288230376151711744), (-795306175349/1152921504606846976)), (3333/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196631561538989/144115188075855872), (-173838695589/36028797018963968)), (2917/144115188075855872), by norm_num⟩
  | 4 => ⟨((747355313017853/18014398509481984), (-1041956894297/36028797018963968)), (4375/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493094012470365/9007199254740992), (-650283271853/4503599627370496)), (2735/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235605166975601/4503599627370496), (-324437876585/562949953421312)), (10943/4503599627370496), by norm_num⟩
  | 1 => ⟨((556887621273309/562949953421312), (-969802388333/562949953421312)), (2053/281474976710656), by norm_num⟩
  | 0 => ⟨((2203471372772991/2251799813685248), (-1925605050781/562949953421312)), (32887/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203471372772991/2251799813685248), (-1925605050781/562949953421312)), (125453957564543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2156153816980357/2251799813685248), (-7537109789025/1125899906842624)), (16147/562949953421312), by norm_num⟩
  | 2 => ⟨((516117376656919/562949953421312), (-14433936748587/1125899906842624)), (124555/2251799813685248), by norm_num⟩
  | 3 => ⟨((473088345129299/562949953421312), (-6616578902119/281474976710656)), (231581/2251799813685248), by norm_num⟩
  | 4 => ⟨((1589039767905169/2251799813685248), (-88966384146855/2251799813685248)), (400117/2251799813685248), by norm_num⟩
  | 5 => ⟨((558915661858161/1125899906842624), (-125562780098747/2251799813685248)), (596323/2251799813685248), by norm_num⟩
  | 6 => ⟨((1095817531413753/4503599627370496), (-3895717323379/70368744177664)), (1317107/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-13553091143/268435456)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1659352607/1073741824), (-120707380907/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((905349604228335/4503599627370496), (320167314993719/4503599627370496)), (1242655/4503599627370496), by norm_num⟩
  | 1 => ⟨((-24752330419/68719476736), (-17506799877/137438953472)), (69/137438953472), by norm_num⟩
  | 2 => ⟨((88700444827/274877906944), (31367974455/274877906944)), (63/137438953472), by norm_num⟩
  | 3 => ⟨((-6622077581/34359738368), (-18734621753/274877906944)), (77/274877906944), by norm_num⟩
  | 4 => ⟨((47460680847/549755813888), (4195991991/137438953472)), (35/274877906944), by norm_num⟩
  | 5 => ⟨((-68030499459/2199023255552), (-24058266825/2199023255552)), (51/1099511627776), by norm_num⟩
  | 6 => ⟨((20315715267/2199023255552), (14368875799/4398046511104)), (123/8796093022208), by norm_num⟩
  | 7 => ⟨((-41601000233/17592186044416), (-29423507743/35184372088832)), (1/274877906944), by norm_num⟩
  | 8 => ⟨((74538986097/140737488355328), (6589981077/35184372088832)), (29/35184372088832), by norm_num⟩
  | 9 => ⟨((-59358192963/562949953421312), (-1311962333/35184372088832)), (47/281474976710656), by norm_num⟩
  | 10 => ⟨((42542241727/2251799813685248), (7522306987/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 11 => ⟨((-55436701423/18014398509481984), (-4901150827/4503599627370496)), (45/9007199254740992), by norm_num⟩
  | 12 => ⟨((16554872453/36028797018963968), (5854455603/36028797018963968)), (109/144115188075855872), by norm_num⟩
  | 13 => ⟨((-73015014103/1152921504606846976), (-12910493863/576460752303423488)), (61/576460752303423488), by norm_num⟩
  | 14 => ⟨((9344667351/1152921504606846976), (6609285609/2305843009213693952)), (127/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-17859622627/18446744073709551616), (-12631733413/36893488147419103232)), (123/73786976294838206464), by norm_num⟩
  | 16 => ⟨((64000295917/590295810358705651712), (22633027955/590295810358705651712)), (7/36893488147419103232), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (221387567039/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444896284133195/158456325028528675187087900672), (524459023691/633825300114114700748351602688)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945330079623161/19807040628566084398385987584), (589935850257/39614081257132168796771975168)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945246253076203/1237940039285380274899124224), (626708017679/2475880078570760549798248448)), (431/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886079309915523/77371252455336267181195264), (626596870253/154742504910672534362390528)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550460717730467/9671406556917033397649408), (293658249597/4835703278458516698824704)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259582420135575/604462909807314587353088), (64222987629/75557863725914323419136)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889081596277165/75557863725914323419136), (834677587777/75557863725914323419136)), (1149/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649253189863813/2361183241434822606848), (625814661491/4722366482869645213696)), (431/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622777252798903/590295810358705651712), (107522599673/73786976294838206464)), (1185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825135461931337/73786976294838206464), (1074754668659/73786976294838206464)), (2963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824524532627107/9223372036854775808), (604225637815/4611686018427387904)), (3333/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595772021075043/1152921504606846976), (1207642141281/1152921504606846976)), (1667/576460752303423488), by norm_num⟩
  | 5 => ⟨((598071254345303/72057594037927936), (527888658677/72057594037927936)), (2919/144115188075855872), by norm_num⟩
  | 4 => ⟨((186747216609945/4503599627370496), (1581848661655/36028797018963968)), (2189/18014398509481984), by norm_num⟩
  | 3 => ⟨((186522386945423/1125899906842624), (1974134568575/9007199254740992)), (2737/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233778927118127/4503599627370496), (3938756507373/4503599627370496)), (10953/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112410046956591/1125899906842624), (2942204801201/1125899906842624)), (4111/562949953421312), by norm_num⟩
  | 0 => ⟨((274755795909229/281474976710656), (11674256312721/2251799813685248)), (16473/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274755795909229/281474976710656), (11674256312721/2251799813685248)), (62839512351607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1072757781367447/1125899906842624), (11395576339801/1125899906842624)), (64661/2251799813685248), by norm_num⟩
  | 2 => ⟨((2044017219170319/2251799813685248), (21715417360625/1125899906842624)), (7783/140737488355328), by norm_num⟩
  | 3 => ⟨((927284949905389/1125899906842624), (39423297521235/1125899906842624)), (230879/2251799813685248), by norm_num⟩
  | 4 => ⟨((762326363753367/1125899906842624), (129875241111263/2251799813685248)), (396471/2251799813685248), by norm_num⟩
  | 5 => ⟨((512411970907681/1125899906842624), (175872330561939/2251799813685248)), (291311/1125899906842624), by norm_num⟩
  | 6 => ⟨((905349604228335/4503599627370496), (320167314993719/4503599627370496)), (1242655/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-120707380907/2147483648)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-901055955/536870912), (-65546107501/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-5643483020313/140737488355328), (1642234749690267/9007199254740992)), (4442191/9007199254740992), by norm_num⟩
  | 1 => ⟨((21448654073/274877906944), (-97523232011/274877906944)), (133/137438953472), by norm_num⟩
  | 2 => ⟨((-10434288411/137438953472), (94885723469/274877906944)), (65/68719476736), by norm_num⟩
  | 3 => ⟨((13536125145/274877906944), (-61546364099/274877906944)), (85/137438953472), by norm_num⟩
  | 4 => ⟨((-13170041649/549755813888), (59881847269/549755813888)), (167/549755813888), by norm_num⟩
  | 5 => ⟨((20502174167/2199023255552), (-23304938869/549755813888)), (131/1099511627776), by norm_num⟩
  | 6 => ⟨((-6649231465/2199023255552), (60465756091/4398046511104)), (171/4398046511104), by norm_num⟩
  | 7 => ⟨((7393603995/8796093022208), (-262636001/68719476736)), (3/274877906944), by norm_num⟩
  | 8 => ⟨((-3596822263/17592186044416), (65416455661/70368744177664)), (47/17592186044416), by norm_num⟩
  | 9 => ⟨((388838497/8796093022208), (-56575353327/281474976710656)), (41/70368744177664), by norm_num⟩
  | 10 => ⟨((-4842526577/562949953421312), (22018110845/562949953421312)), (257/2251799813685248), by norm_num⟩
  | 11 => ⟨((6853179355/4503599627370496), (-62320385973/9007199254740992)), (183/9007199254740992), by norm_num⟩
  | 12 => ⟨((-8890447507/36028797018963968), (40423290519/36028797018963968)), (239/72057594037927936), by norm_num⟩
  | 13 => ⟨((21292322503/576460752303423488), (-24203105009/144115188075855872)), (9/18014398509481984), by norm_num⟩
  | 14 => ⟨((-23675969403/4611686018427387904), (107650440401/4611686018427387904)), (161/2305843009213693952), by norm_num⟩
  | 15 => ⟨((1535710305/2305843009213693952), (-111721645081/36893488147419103232)), (21/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-5976708537/73786976294838206464), (27175035379/73786976294838206464)), (329/295147905179352825856), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (291017035157/1267650600228229401496703205376)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779376103665251/633825300114114700748351602688), (344628768869/79228162514264337593543950336)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945212402295265/19807040628566084398385987584), (1550596804909/19807040628566084398385987584)), (1627/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472560548455333/618970019642690137449562112), (3294453260725/2475880078570760549798248448)), (1729/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771908028675811/154742504910672534362390528), (3293817778241/154742504910672534362390528)), (1729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775112746218907/4835703278458516698824704), (771819768857/2417851639229258349412352)), (1621/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259376302106687/604462909807314587353088), (1350347110639/302231454903657293676544)), (1419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888746100068603/75557863725914323419136), (4387362800511/75557863725914323419136)), (1153/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649127136428819/2361183241434822606848), (411176901767/590295810358705651712)), (1731/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811214909468173/295147905179352825856), (4521147715297/590295810358705651712)), (595/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824699990528495/73786976294838206464), (5648738188521/73786976294838206464)), (93/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1824033008182009/9223372036854775808), (6351124218035/9223372036854775808)), (3351/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595278475897301/1152921504606846976), (24790990183/4503599627370496)), (1677/576460752303423488), by norm_num⟩
  | 5 => ⟨((597854193840689/72057594037927936), (5547975080441/144115188075855872)), (2937/144115188075855872), by norm_num⟩
  | 4 => ⟨((746661012129663/18014398509481984), (1038944538873/4503599627370496)), (4411/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491351561731549/9007199254740992), (2592812599041/2251799813685248)), (1381/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116050131313917/2251799813685248), (10343990015125/2251799813685248)), (5539/2251799813685248), by norm_num⟩
  | 1 => ⟨((555560861255613/562949953421312), (15447946487743/1125899906842624)), (8347/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096330247016327/1125899906842624), (7656103414845/281474976710656)), (16847/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096330247016327/1125899906842624), (7656103414845/281474976710656)), (64266209128951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1066704196804569/1125899906842624), (59640241175739/1125899906842624)), (33727/1125899906842624), by norm_num⟩
  | 2 => ⟨((251865391901025/281474976710656), (56504574850711/562949953421312)), (134963/2251799813685248), by norm_num⟩
  | 3 => ⟨((1780278577504419/2251799813685248), (404484890423621/2251799813685248)), (268625/2251799813685248), by norm_num⟩
  | 4 => ⟨((333709036730595/562949953421312), (639573536660793/2251799813685248)), (521257/2251799813685248), by norm_num⟩
  | 5 => ⟨((609616015593857/2251799813685248), (758260898825303/2251799813685248)), (228523/562949953421312), by norm_num⟩
  | 6 => ⟨((-5643483020313/140737488355328), (1642234749690267/9007199254740992)), (4442191/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-65546107501/1073741824)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1925775643/1073741824), (-70043983737/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-138342416128235/1125899906842624), (-15786783612699/140737488355328)), (4241779/4503599627370496), by norm_num⟩
  | 1 => ⟨((35116573129/137438953472), (4007286823/17179869184)), (541/274877906944), by norm_num⟩
  | 2 => ⟨((-36511430483/137438953472), (-33331674757/137438953472)), (283/137438953472), by norm_num⟩
  | 3 => ⟨((50615590195/274877906944), (46207512763/274877906944)), (395/274877906944), by norm_num⟩
  | 4 => ⟨((-26313040227/274877906944), (-48042910789/549755813888)), (413/549755813888), by norm_num⟩
  | 5 => ⟨((43773143149/1099511627776), (39960969791/1099511627776)), (173/549755813888), by norm_num⟩
  | 6 => ⟨((-15170615379/1099511627776), (-27698833543/2199023255552)), (241/2199023255552), by norm_num⟩
  | 7 => ⟨((18026518761/4398046511104), (32913202929/8796093022208)), (9/274877906944), by norm_num⟩
  | 8 => ⟨((-9371272991/8796093022208), (-2138783795/2199023255552)), (151/17592186044416), by norm_num⟩
  | 9 => ⟨((69287162155/281474976710656), (15813247545/70368744177664)), (561/281474976710656), by norm_num⟩
  | 10 => ⟨((-14407860329/281474976710656), (-52612358167/1125899906842624)), (469/1125899906842624), by norm_num⟩
  | 11 => ⟨((43578622975/4503599627370496), (39783390247/4503599627370496)), (357/4503599627370496), by norm_num⟩
  | 12 => ⟨((-943949989/562949953421312), (-27575744783/18014398509481984)), (497/36028797018963968), by norm_num⟩
  | 13 => ⟨((38653810617/144115188075855872), (17643738229/72057594037927936)), (5/2251799813685248), by norm_num⟩
  | 14 => ⟨((-22965239869/576460752303423488), (-41930425399/1152921504606846976)), (191/576460752303423488), by norm_num⟩
  | 15 => ⟨((12734633013/2305843009213693952), (5812791229/1152921504606846976)), (213/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-52961849811/73786976294838206464), (-48349438219/73786976294838206464)), (445/73786976294838206464), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-3128469633613/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444798796542805/158456325028528675187087900672), (-1852049384379/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890221116855749/39614081257132168796771975168), (-1041609441103/9903520314283042199192993792)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890025572483855/2475880078570760549798248448), (-4426028268355/2475880078570760549798248448)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221461397375043/19342813113834066795298816), (-4425114970183/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550021953417395/9671406556917033397649408), (-1036893753543/2417851639229258349412352)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259197963193427/604462909807314587353088), (-3628157989381/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888455845458395/75557863725914323419136), (-5893937965389/75557863725914323419136)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298036185139017/4722366482869645213696), (-4418862312995/4722366482869645213696)), (1733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811064652150059/295147905179352825856), (-1518337633083/147573952589676412928)), (149/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1824323382446407/73786976294838206464), (-7587811299389/73786976294838206464)), (5963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823607999534401/9223372036854775808), (-2132739603425/2305843009213693952)), (3357/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594851814593393/1152921504606846976), (-2131074720727/288230376151711744)), (3361/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195333203975617/144115188075855872), (-7451272431303/144115188075855872)), (5889/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492755548994395/36028797018963968), (-11161937680503/36028797018963968)), (8849/36028797018963968), by norm_num⟩
  | 3 => ⟨((372659254147141/2251799813685248), (-13926239183227/9007199254740992)), (693/562949953421312), by norm_num⟩
  | 2 => ⟨((1115325956355389/2251799813685248), (-13886997449129/2251799813685248)), (5565/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110011548934225/1125899906842624), (-20732506507863/1125899906842624)), (8399/562949953421312), by norm_num⟩
  | 0 => ⟨((1094015233136965/1125899906842624), (-41073745731525/1125899906842624)), (34011/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094015233136965/1125899906842624), (-41073745731525/1125899906842624)), (129741672996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((530767553351601/562949953421312), (-39910566862285/562949953421312)), (34289/562949953421312), by norm_num⟩
  | 2 => ⟨((995190924667979/1125899906842624), (-150515929862895/1125899906842624)), (4345/35184372088832), by norm_num⟩
  | 3 => ⟨((429767302367441/562949953421312), (-266084198972143/1125899906842624)), (565945/2251799813685248), by norm_num⟩
  | 4 => ⟨((1186604478309943/2251799813685248), (-203134022304957/562949953421312)), (141451/281474976710656), by norm_num⟩
  | 5 => ⟨((83024175496833/562949953421312), (-13380393491201/35184372088832)), (2009277/2251799813685248), by norm_num⟩
  | 6 => ⟨((-138342416128235/1125899906842624), (-15786783612699/140737488355328)), (4241779/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-70043983737/1073741824)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile062Terms0

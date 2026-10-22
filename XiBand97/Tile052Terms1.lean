/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile052Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨52,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76729/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76729/2560))
  have he : value ((69/80), (76729/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-8839015673/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-168055667305701/1125899906842624), (-39725958498347/2251799813685248)), (14089149/4503599627370496), by norm_num⟩
  | 1 => ⟨((11268800127/34359738368), (332972917/8589934592)), (475/68719476736), by norm_num⟩
  | 2 => ⟨((-6190021149/17179869184), (-2926465107/68719476736)), (131/17179869184), by norm_num⟩
  | 3 => ⟨((4533622201/17179869184), (2143367019/68719476736)), (193/34359738368), by norm_num⟩
  | 4 => ⟨((-19922772249/137438953472), (-1177364673/68719476736)), (213/68719476736), by norm_num⟩
  | 5 => ⟨((17509921933/274877906944), (2069547677/274877906944)), (377/274877906944), by norm_num⟩
  | 6 => ⟨((-25648820545/1099511627776), (-3031507347/1099511627776)), (555/1099511627776), by norm_num⟩
  | 7 => ⟨((16101776823/2199023255552), (1903114985/2199023255552)), (175/1099511627776), by norm_num⟩
  | 8 => ⟨((-17689609887/8796093022208), (-2090785509/8796093022208)), (193/4398046511104), by norm_num⟩
  | 9 => ⟨((2159335867/4398046511104), (2041744581/35184372088832)), (379/35184372088832), by norm_num⟩
  | 10 => ⟨((-30365093361/281474976710656), (-3588937099/281474976710656)), (669/281474976710656), by norm_num⟩
  | 11 => ⟨((12130714441/562949953421312), (716881891/281474976710656)), (537/1125899906842624), by norm_num⟩
  | 12 => ⟨((-17769269273/4503599627370496), (-262525085/562949953421312)), (395/4503599627370496), by norm_num⟩
  | 13 => ⟨((24026507795/36028797018963968), (1419880785/18014398509481984)), (67/4503599627370496), by norm_num⟩
  | 14 => ⟨((-30166647677/288230376151711744), (-3565482237/288230376151711744)), (169/72057594037927936), by norm_num⟩
  | 15 => ⟨((8837719959/576460752303423488), (32642355/18014398509481984)), (199/576460752303423488), by norm_num⟩
  | 16 => ⟨((-19418455501/9223372036854775808), (-2295122709/9223372036854775808)), (55/1152921504606846976), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1969513382923/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779034226803571/633825300114114700748351602688), (-4663014452349/633825300114114700748351602688)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890039823679819/39614081257132168796771975168), (-2622493071347/19807040628566084398385987584)), (13035/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944916334083461/1237940039285380274899124224), (-5571716599531/2475880078570760549798248448)), (6927/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885748979778289/77371252455336267181195264), (-5570500177739/154742504910672534362390528)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549840475595399/9671406556917033397649408), (-5221051529429/9671406556917033397649408)), (6499/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259038835762807/604462909807314587353088), (-2283563884613/302231454903657293676544)), (5689/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888196637049125/75557863725914323419136), (-7419159672225/75557863725914323419136)), (9249/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324460307833847/1180591620717411303424), (-2781124908249/2361183241434822606848)), (13883/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621860354161489/590295810358705651712), (-7644648873985/590295810358705651712)), (19101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823985863575531/73786976294838206464), (-2387661160183/18446744073709551616)), (23897/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455806615829015/2305843009213693952), (-10737372140575/9223372036854775808)), (841/288230376151711744), by norm_num⟩
  | 6 => ⟨((398616999593545/288230376151711744), (-2682123621223/288230376151711744)), (26947/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194994805774027/144115188075855872), (-9377446967665/144115188075855872)), (23619/144115188075855872), by norm_num⟩
  | 4 => ⟨((746121424319761/18014398509481984), (-14046203218507/36028797018963968)), (17753/18014398509481984), by norm_num⟩
  | 3 => ⟨((744993622224423/4503599627370496), (-17522820881193/9007199254740992)), (22261/4503599627370496), by norm_num⟩
  | 2 => ⟨((139332863298407/281474976710656), (-17470440474799/2251799813685248)), (44731/2251799813685248), by norm_num⟩
  | 1 => ⟨((554492007162119/562949953421312), (-26074778502473/1125899906842624)), (67619/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091829732015857/1125899906842624), (-1613326588551/35184372088832)), (17167/140737488355328), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1091829732015857/1125899906842624), (-1613326588551/35184372088832)), (65486908495855287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((528211640332961/562949953421312), (-25032107044349/281474976710656)), (69739/281474976710656), by norm_num⟩
  | 2 => ⟨((982329280855219/1125899906842624), (-46974869586641/281474976710656)), (286551/562949953421312), by norm_num⟩
  | 3 => ⟨((206427009277781/281474976710656), (-163939226138555/562949953421312)), (1191333/1125899906842624), by norm_num⟩
  | 4 => ⟨((1020143051068829/2251799813685248), (-120229103668719/281474976710656)), (4882515/2251799813685248), by norm_num⟩
  | 5 => ⟨((12830786769621/562949953421312), (-217871737795643/562949953421312)), (8594927/2251799813685248), by norm_num⟩
  | 6 => ⟨((-168055667305701/1125899906842624), (-39725958498347/2251799813685248)), (14089149/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-8839015673/134217728)), (1/134217728), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-9262860945/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1229859795251321/9007199254740992), (125070297400539/9007199254740992)), (2620217/2251799813685248), by norm_num⟩
  | 1 => ⟨((-21605353019/68719476736), (-1098575601/34359738368)), (93/34359738368), by norm_num⟩
  | 2 => ⟨((24874081895/68719476736), (1264781901/34359738368)), (217/68719476736), by norm_num⟩
  | 3 => ⟨((-19091563391/68719476736), (-1941511967/68719476736)), (169/68719476736), by norm_num⟩
  | 4 => ⟨((21979974633/137438953472), (2235248257/137438953472)), (197/137438953472), by norm_num⟩
  | 5 => ⟨((-20244304773/274877906944), (-1029369863/137438953472)), (23/34359738368), by norm_num⟩
  | 6 => ⟨((15538078129/549755813888), (3160282269/1099511627776)), (285/1099511627776), by norm_num⟩
  | 7 => ⟨((-20444426899/2199023255552), (-1039545549/1099511627776)), (95/1099511627776), by norm_num⟩
  | 8 => ⟨((11768758153/4398046511104), (2393642085/8796093022208)), (221/8796093022208), by norm_num⟩
  | 9 => ⟨((-24087615187/35184372088832), (-2449584259/35184372088832)), (57/8796093022208), by norm_num⟩
  | 10 => ⟨((11092756731/70368744177664), (2256150479/140737488355328)), (53/35184372088832), by norm_num⟩
  | 11 => ⟨((-9288005923/281474976710656), (-1889083077/562949953421312)), (45/140737488355328), by norm_num⟩
  | 12 => ⟨((28515231975/4503599627370496), (362481211/562949953421312)), (279/4503599627370496), by norm_num⟩
  | 13 => ⟨((-20202691713/18014398509481984), (-256813487/2251799813685248)), (25/2251799813685248), by norm_num⟩
  | 14 => ⟨((26581952443/144115188075855872), (337905661/18014398509481984)), (133/72057594037927936), by norm_num⟩
  | 15 => ⟨((-16321921983/576460752303423488), (-1659853947/576460752303423488)), (165/576460752303423488), by norm_num⟩
  | 16 => ⟨((18791307123/4611686018427387904), (1910977477/4611686018427387904)), (3/72057594037927936), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (16501867057/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778905726902803/633825300114114700748351602688), (19531958591/79228162514264337593543950336)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((59059248429599/1237940039285380274899124224), (10984819465/2475880078570760549798248448)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889680689689053/2475880078570760549798248448), (186704108041/2475880078570760549798248448)), (13779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885673489477873/77371252455336267181195264), (186661572559/154742504910672534362390528)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699990919317/9671406556917033397649408), (174950044035/9671406556917033397649408)), (6459/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157364621328223/75557863725914323419136), (19129515465/75557863725914323419136)), (1413/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944000295145547/37778931862957161709568), (124299524897/37778931862957161709568)), (18369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648847965447851/2361183241434822606848), (93187625129/2361183241434822606848)), (13777/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810831691055985/295147905179352825856), (256145720223/590295810358705651712)), (37/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1823743867844139/73786976294838206464), (160000942159/36893488147419103232)), (185/576460752303423488), by norm_num⟩
  | 7 => ⟨((911480005989995/4611686018427387904), (359754428507/9223372036854775808)), (26641/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398552194449115/288230376151711744), (359445075627/1152921504606846976)), (13321/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194776106477065/144115188075855872), (78541694537/36028797018963968)), (11657/72057594037927936), by norm_num⟩
  | 4 => ⟨((745965498706163/18014398509481984), (235277868785/18014398509481984)), (8743/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489625687203021/9007199254740992), (73372679275/1125899906842624)), (5465/1125899906842624), by norm_num⟩
  | 2 => ⟨((2228687112290853/4503599627370496), (585165598891/2251799813685248)), (2733/140737488355328), by norm_num⟩
  | 1 => ⟨((1108609884015299/1125899906842624), (1746445707297/2251799813685248)), (65611/1125899906842624), by norm_num⟩
  | 0 => ⟨((68218582889265/70368744177664), (1728427541871/1125899906842624)), (131301/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((68218582889265/70368744177664), (1728427541871/1125899906842624)), (500873569968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058143284728201/1125899906842624), (3351228699933/1125899906842624)), (509963/2251799813685248), by norm_num⟩
  | 2 => ⟨((994454279174295/1125899906842624), (12598207435213/2251799813685248)), (60099/140737488355328), by norm_num⟩
  | 3 => ⟨((1756638629509449/2251799813685248), (695462648241/70368744177664)), (427351/562949953421312), by norm_num⟩
  | 4 => ⟨((171267666623823/281474976710656), (8680534003823/562949953421312)), (168801/140737488355328), by norm_num⟩
  | 5 => ⟨((1666295231252723/4503599627370496), (42254407727669/2251799813685248)), (6739993/4503599627370496), by norm_num⟩
  | 6 => ⟨((1229859795251321/9007199254740992), (125070297400539/9007199254740992)), (2620217/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-9262860945/134217728)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-602892227/8388608)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-263687010329885/2251799813685248), (-214488001292479/4503599627370496)), (25195351/9007199254740992), by norm_num⟩
  | 1 => ⟨((19296076525/68719476736), (7847896795/68719476736)), (463/68719476736), by norm_num⟩
  | 2 => ⟨((-11567492671/34359738368), (-9409217313/68719476736)), (279/34359738368), by norm_num⟩
  | 3 => ⟨((18491757329/68719476736), (1880193143/17179869184)), (7/1073741824), by norm_num⟩
  | 4 => ⟨((-22170648743/137438953472), (-9017012499/137438953472)), (135/34359738368), by norm_num⟩
  | 5 => ⟨((10632578763/137438953472), (8648740659/274877906944)), (521/274877906944), by norm_num⟩
  | 6 => ⟨((-8498603451/274877906944), (-6912924781/549755813888)), (419/549755813888), by norm_num⟩
  | 7 => ⟨((11645006309/1099511627776), (4736134187/1099511627776)), (577/2199023255552), by norm_num⟩
  | 8 => ⟨((-6980876395/2199023255552), (-5678376889/4398046511104)), (87/1099511627776), by norm_num⟩
  | 9 => ⟨((14879476007/17592186044416), (378226475/1099511627776)), (373/17592186044416), by norm_num⟩
  | 10 => ⟨((-1783971259/8796093022208), (-5804463849/70368744177664)), (45/8796093022208), by norm_num⟩
  | 11 => ⟨((12444439997/281474976710656), (5061271427/281474976710656)), (79/70368744177664), by norm_num⟩
  | 12 => ⟨((-19893642561/2251799813685248), (-8090932553/2251799813685248)), (507/2251799813685248), by norm_num⟩
  | 13 => ⟨((7338903301/4503599627370496), (5969602745/9007199254740992)), (47/1125899906842624), by norm_num⟩
  | 14 => ⟨((-5027977581/18014398509481984), (-2044926029/18014398509481984)), (259/36028797018963968), by norm_num⟩
  | 15 => ⟨((12860334585/288230376151711744), (5230419689/288230376151711744)), (333/288230376151711744), by norm_num⟩
  | 16 => ⟨((-7709433877/1152921504606846976), (-1567749831/576460752303423488)), (401/2305843009213693952), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-3589106302385/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444692336902979/158456325028528675187087900672), (-4247565814849/633825300114114700748351602688)), (5789/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472435500988617/9903520314283042199192993792), (-4777623358793/39614081257132168796771975168)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889516444947713/2475880078570760549798248448), (-317196945941/154742504910672534362390528)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885590986405093/77371252455336267181195264), (-5073943294573/154742504910672534362390528)), (13851/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774772244596235/4835703278458516698824704), (-1188884669293/2417851639229258349412352)), (6495/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258780098741669/604462909807314587353088), (-259988335673/37778931862957161709568)), (11371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887776659975291/75557863725914323419136), (-1689322889737/18889465931478580854784)), (9243/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297526660100101/4722366482869645213696), (-5065864550575/4722366482869645213696)), (867/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621428487153739/590295810358705651712), (-6962145322213/590295810358705651712)), (19087/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823447031845555/73786976294838206464), (-8697555328433/73786976294838206464)), (23877/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28478463349749/144115188075855872), (-9777703209163/9223372036854775808)), (26887/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593864908855899/1152921504606846976), (-9768898285819/1152921504606846976)), (26919/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597234517332493/72057594037927936), (-1067235616525/18014398509481984)), (23591/144115188075855872), by norm_num⟩
  | 4 => ⟨((745729025553263/18014398509481984), (-1598379557909/4503599627370496)), (17729/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489012989052165/9007199254740992), (-7974593354563/4503599627370496)), (1389/281474976710656), by norm_num⟩
  | 2 => ⟨((556849369657235/1125899906842624), (-248395689029/35184372088832)), (44639/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107562900513089/1125899906842624), (-23716507767667/1125899906842624)), (67435/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089087546190119/1125899906842624), (-11729044162463/281474976710656)), (68391/562949953421312), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089087546190119/1125899906842624), (-11729044162463/281474976710656)), (260890962840843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1051523806370169/1125899906842624), (-45382207950881/562949953421312)), (69005/281474976710656), by norm_num⟩
  | 2 => ⟨((974743962140341/1125899906842624), (-21192146724577/140737488355328)), (140019/281474976710656), by norm_num⟩
  | 3 => ⟨((409176221096755/562949953421312), (-293552447268633/1125899906842624)), (142305/140737488355328), by norm_num⟩
  | 4 => ⟨((518276692981593/1125899906842624), (-106683267612947/281474976710656)), (2248579/1125899906842624), by norm_num⟩
  | 5 => ⟨((307343899914961/4503599627370496), (-785738779070875/2251799813685248)), (7549265/2251799813685248), by norm_num⟩
  | 6 => ⟨((-263687010329885/2251799813685248), (-214488001292479/4503599627370496)), (25195351/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-602892227/8388608)), (1/134217728), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-9996305817/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((639989742995135/9007199254740992), (840373339313901/9007199254740992)), (16224283/9007199254740992), by norm_num⟩
  | 1 => ⟨((-12133138795/68719476736), (-15932077783/68719476736)), (155/34359738368), by norm_num⟩
  | 2 => ⟨((7537429319/34359738368), (9897431507/34359738368)), (97/17179869184), by norm_num⟩
  | 3 => ⟨((-12486538825/68719476736), (-1024758057/4294967296)), (81/17179869184), by norm_num⟩
  | 4 => ⟨((969621355/8589934592), (10185712441/68719476736)), (203/68719476736), by norm_num⟩
  | 5 => ⟨((-7710139369/137438953472), (-10124217831/137438953472)), (203/137438953472), by norm_num⟩
  | 6 => ⟨((12772651059/549755813888), (8385912071/274877906944)), (339/549755813888), by norm_num⟩
  | 7 => ⟨((-4534120793/549755813888), (-11907547811/1099511627776)), (243/1099511627776), by norm_num⟩
  | 8 => ⟨((5633433455/2199023255552), (14794572369/4398046511104)), (19/274877906944), by norm_num⟩
  | 9 => ⟨((-6221580557/8796093022208), (-16339169449/17592186044416)), (169/8796093022208), by norm_num⟩
  | 10 => ⟨((12368037519/70368744177664), (8120262163/35184372088832)), (339/70368744177664), by norm_num⟩
  | 11 => ⟨((-11175788609/281474976710656), (-3668744263/70368744177664)), (309/281474976710656), by norm_num⟩
  | 12 => ⟨((9256930477/1125899906842624), (12155316021/1125899906842624)), (129/562949953421312), by norm_num⟩
  | 13 => ⟨((-7077725569/4503599627370496), (-18587584991/9007199254740992)), (397/9007199254740992), by norm_num⟩
  | 14 => ⟨((10049992761/36028797018963968), (13196689585/36028797018963968)), (71/9007199254740992), by norm_num⟩
  | 15 => ⟨((-13319090049/288230376151711744), (-2186169447/36028797018963968)), (379/288230376151711744), by norm_num⟩
  | 16 => ⟨((4137086929/576460752303423488), (10864853993/1152921504606846976)), (237/1152921504606846976), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (1198326548445/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889331121709743/316912650057057350374175801344), (177249572673/79228162514264337593543950336)), (11543/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889622020169741/39614081257132168796771975168), (1594947423065/39614081257132168796771975168)), (12987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236173702798693/309485009821345068724781056), (1694261153089/2475880078570760549798248448)), (13801/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885527946222101/77371252455336267181195264), (423461126961/38685626227668133590597632)), (6901/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96839192308765/604462909807314587353088), (1587536676761/9671406556917033397649408)), (12941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258678150562695/604462909807314587353088), (347163049025/151115727451828646838272)), (11325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471903117414685/18889465931478580854784), (1127865325815/37778931862957161709568)), (18405/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648702403618393/2361183241434822606848), (1691072793019/4722366482869645213696)), (6903/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621263033327213/590295810358705651712), (2324047257307/590295810358705651712)), (4747/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823243351532029/73786976294838206464), (90727918399/2305843009213693952)), (23741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455599205289877/2305843009213693952), (1631889490413/4611686018427387904)), (26717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593645450242171/1152921504606846976), (3260748975567/1152921504606846976)), (3341/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194283042040601/144115188075855872), (2849750164969/144115188075855872)), (23399/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491191097597059/36028797018963968), (4267823778879/36028797018963968)), (17561/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488700287496095/9007199254740992), (5322897172305/9007199254740992)), (43945/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226834760363111/4503599627370496), (5305113318065/2251799813685248)), (5501/281474976710656), by norm_num⟩
  | 1 => ⟨((2214437436575295/2251799813685248), (7913349955091/1125899906842624)), (16543/281474976710656), by norm_num⟩
  | 0 => ⟨((544353809751029/562949953421312), (15650255181133/1125899906842624)), (66493/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544353809751029/562949953421312), (15650255181133/1125899906842624)), (253650667430686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2105052754818721/2251799813685248), (60533096980645/2251799813685248)), (521767/2251799813685248), by norm_num⟩
  | 2 => ⟨((983120883533099/1125899906842624), (28294114286357/562949953421312)), (1003581/2251799813685248), by norm_num⟩
  | 3 => ⟨((1711207964706857/2251799813685248), (98824183098109/1125899906842624)), (1853509/2251799813685248), by norm_num⟩
  | 4 => ⟨((20047628986165/35184372088832), (300397447757797/2251799813685248)), (3142449/2251799813685248), by norm_num⟩
  | 5 => ⟨((1381982704569679/4503599627370496), (684651306646537/4503599627370496)), (8838971/4503599627370496), by norm_num⟩
  | 6 => ⟨((639989742995135/9007199254740992), (840373339313901/9007199254740992)), (16224283/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-9996305817/134217728)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-10318302373/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((180506736849385/18014398509481984), (-490858184363269/4503599627370496)), (38605773/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1766169123/68719476736), (9605609013/34359738368)), (95/17179869184), by norm_num⟩
  | 2 => ⟨((2265067179/68719476736), (-24637900665/68719476736)), (245/34359738368), by norm_num⟩
  | 3 => ⟨((-968297101/34359738368), (2633123645/8589934592)), (421/68719476736), by norm_num⟩
  | 4 => ⟨((2483633027/137438953472), (-27015315205/137438953472)), (271/68719476736), by norm_num⟩
  | 5 => ⟨((-2548157175/274877906944), (13858583075/137438953472)), (279/137438953472), by norm_num⟩
  | 6 => ⟨((1089315685/274877906944), (-23697709169/549755813888)), (15/17179869184), by norm_num⟩
  | 7 => ⟨((-798297019/549755813888), (271354571/17179869184)), (177/549755813888), by norm_num⟩
  | 8 => ⟨((1023795713/2199023255552), (-22272343441/4398046511104)), (57/549755813888), by norm_num⟩
  | 9 => ⟨((-2334208139/17592186044416), (25389970221/17592186044416)), (261/8796093022208), by norm_num⟩
  | 10 => ⟨((1197425133/35184372088832), (-26049595121/70368744177664)), (269/35184372088832), by norm_num⟩
  | 11 => ⟨((-2233698055/281474976710656), (24296688097/281474976710656)), (63/35184372088832), by norm_num⟩
  | 12 => ⟨((954887065/562949953421312), (-10386629087/562949953421312)), (433/1125899906842624), by norm_num⟩
  | 13 => ⟨((-1507222747/4503599627370496), (1024660677/281474976710656)), (343/4503599627370496), by norm_num⟩
  | 14 => ⟨((2209114295/36028797018963968), (-375457535/562949953421312)), (505/36028797018963968), by norm_num⟩
  | 15 => ⟨((-188875543/18014398509481984), (513615767/4503599627370496)), (347/144115188075855872), by norm_num⟩
  | 16 => ⟨((1937824811/1152921504606846976), (-2634796863/144115188075855872)), (447/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-60209957547/316912650057057350374175801344)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444638532423993/158456325028528675187087900672), (-2279653348545/633825300114114700748351602688)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236187539942319/4951760157141521099596496896), (-1282056330293/19807040628566084398385987584)), (1625/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944630109209663/1237940039285380274899124224), (-1361877327381/1237940039285380274899124224)), (13815/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770926379410565/154742504910672534362390528), (-680765736611/38685626227668133590597632)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549305542683569/9671406556917033397649408), (-638034196041/2417851639229258349412352)), (3239/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258571692404301/604462909807314587353088), (-1116192598219/302231454903657293676544)), (11339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887439258464709/75557863725914323419136), (-3626249282511/75557863725914323419136)), (9215/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297274709460789/4722366482869645213696), (-1359241444613/2361183241434822606848)), (13827/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621083841554739/590295810358705651712), (-1867979151815/295147905179352825856)), (9509/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911509450771215/36893488147419103232), (-4667016036013/73786976294838206464)), (23783/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822143683215955/9223372036854775808), (-5246364451927/9223372036854775808)), (26769/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593391524422089/1152921504606846976), (-2620666379123/576460752303423488)), (13393/576460752303423488), by norm_num⟩
  | 5 => ⟨((597029986498253/72057594037927936), (-4580511062097/144115188075855872)), (23457/144115188075855872), by norm_num⟩
  | 4 => ⟨((372713683035247/9007199254740992), (-3429735132039/18014398509481984)), (4403/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488276760868481/9007199254740992), (-8554600438673/9007199254740992)), (22049/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225978551536571/4503599627370496), (-17050113284353/4503599627370496)), (5525/281474976710656), by norm_num⟩
  | 1 => ⟨((138320651388841/140737488355328), (-25427886274697/2251799813685248)), (16639/281474976710656), by norm_num⟩
  | 0 => ⟨((543677881854523/562949953421312), (-50269244298981/2251799813685248)), (268281/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543677881854523/562949953421312), (-50269244298981/2251799813685248)), (1023410805709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099140075345725/2251799813685248), (-97096646324593/2251799813685248)), (530173/2251799813685248), by norm_num⟩
  | 2 => ⟨((976321534106311/1125899906842624), (-181028047202879/2251799813685248)), (1034183/2251799813685248), by norm_num⟩
  | 3 => ⟨((419669165859195/562949953421312), (-313956115791897/2251799813685248)), (1959861/2251799813685248), by norm_num⟩
  | 4 => ⟨((1207650378686911/2251799813685248), (-468097387449895/2251799813685248)), (3468589/2251799813685248), by norm_num⟩
  | 5 => ⟨((1100723310725391/4503599627370496), (-1004170945890727/4503599627370496)), (645315/281474976710656), by norm_num⟩
  | 6 => ⟨((180506736849385/18014398509481984), (-490858184363269/4503599627370496)), (38605773/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-10318302373/134217728)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-2654106155/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-784185883070525/9007199254740992), (245118958013859/4503599627370496)), (20943837/9007199254740992), by norm_num⟩
  | 1 => ⟨((3947279935/17179869184), (-4935325491/34359738368)), (53/8589934592), by norm_num⟩
  | 2 => ⟨((-20834196089/68719476736), (13024606911/68719476736)), (281/34359738368), by norm_num⟩
  | 3 => ⟨((18327545965/68719476736), (-11457561445/68719476736)), (497/68719476736), by norm_num⟩
  | 4 => ⟨((-1511482641/8589934592), (3779645189/34359738368)), (165/34359738368), by norm_num⟩
  | 5 => ⟨((12764445895/137438953472), (-498735017/8589934592)), (351/137438953472), by norm_num⟩
  | 6 => ⟨((-11228701499/274877906944), (7019681611/274877906944)), (311/274877906944), by norm_num⟩
  | 7 => ⟨((8466624855/549755813888), (-10585909833/1099511627776)), (471/1099511627776), by norm_num⟩
  | 8 => ⟨((-5585977095/1099511627776), (3492102867/1099511627776)), (313/2199023255552), by norm_num⟩
  | 9 => ⟨((3275936399/2199023255552), (-2047968815/2199023255552)), (369/8796093022208), by norm_num⟩
  | 10 => ⟨((-1729076793/4398046511104), (8647531379/35184372088832)), (49/4398046511104), by norm_num⟩
  | 11 => ⟨((13274568099/140737488355328), (-8298665843/140737488355328)), (189/70368744177664), by norm_num⟩
  | 12 => ⟨((-5838724373/281474976710656), (3650109153/281474976710656)), (335/562949953421312), by norm_num⟩
  | 13 => ⟨((18964588741/4503599627370496), (-11855812079/4503599627370496)), (273/2251799813685248), by norm_num⟩
  | 14 => ⟨((-14299610549/18014398509481984), (1117434563/2251799813685248)), (207/9007199254740992), by norm_num⟩
  | 15 => ⟨((1257916401/9007199254740992), (-786393033/9007199254740992)), (585/144115188075855872), by norm_num⟩
  | 16 => ⟨((-1659856749/72057594037927936), (8301345191/576460752303423488)), (97/144115188075855872), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (1682245904317/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778449919455171/633825300114114700748351602688), (1990188288391/316912650057057350374175801344)), (11575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889382786721641/39614081257132168796771975168), (4477017274835/39614081257132168796771975168)), (13025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889134948139007/2475880078570760549798248448), (4755724332375/2475880078570760549798248448)), (6921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885400334458187/77371252455336267181195264), (1188619919249/38685626227668133590597632)), (13847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774593610855815/4835703278458516698824704), (1114000629087/2417851639229258349412352)), (6493/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258467694556697/604462909807314587353088), (1948840159615/302231454903657293676544)), (11367/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887269387163523/75557863725914323419136), (6331252622873/75557863725914323419136)), (18479/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297146541356289/4722366482869645213696), (4746271942373/4722366482869645213696)), (13867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810453184713367/295147905179352825856), (6522602882287/590295810358705651712)), (9539/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455698800648495/18446744073709551616), (4073987063541/36893488147419103232)), (23865/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910944735214551/4611686018427387904), (4579607499091/4611686018427387904)), (26871/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593134128837693/1152921504606846976), (4575075104253/576460752303423488)), (13451/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193831180194331/144115188075855872), (7996190530963/144115188075855872)), (23573/144115188075855872), by norm_num⟩
  | 4 => ⟨((372626105506823/9007199254740992), (5986960735675/18014398509481984)), (17713/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487826461992075/9007199254740992), (14931803624425/9007199254740992)), (22201/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112520460536565/2251799813685248), (14878485082455/2251799813685248)), (11145/562949953421312), by norm_num⟩
  | 1 => ⟨((1105816048113693/1125899906842624), (11092353659933/562949953421312)), (67317/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085675773576173/1125899906842624), (43838992266043/1125899906842624)), (136429/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085675773576173/1125899906842624), (43838992266043/1125899906842624)), (520435337546920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045181743897067/1125899906842624), (84545582696969/1125899906842624)), (273735/1125899906842624), by norm_num⟩
  | 2 => ⟨((1927803556295771/2251799813685248), (313937319027999/2251799813685248)), (1098663/2251799813685248), by norm_num⟩
  | 3 => ⟨((1606656990288673/2251799813685248), (537533999601557/2251799813685248)), (273439/281474976710656), by norm_num⟩
  | 4 => ⟨((1018031829376569/2251799813685248), (191764994545467/562949953421312)), (4165951/2251799813685248), by norm_num⟩
  | 5 => ⟨((397910855816473/4503599627370496), (1387141908590973/4503599627370496)), (13210065/4503599627370496), by norm_num⟩
  | 6 => ⟨((-784185883070525/9007199254740992), (245118958013859/4503599627370496)), (20943837/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-2654106155/33554432)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-21787939583/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((379178926400403/4503599627370496), (107298825858925/2251799813685248)), (5213741/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3917066833/17179869184), (-4433755599/34359738368)), (217/68719476736), by norm_num⟩
  | 2 => ⟨((21215227249/68719476736), (12006832741/68719476736)), (37/8589934592), by norm_num⟩
  | 3 => ⟨((-37403581/134217728), (-5419184303/34359738368)), (135/34359738368), by norm_num⟩
  | 4 => ⟨((6482609603/34359738368), (7337711571/68719476736)), (185/68719476736), by norm_num⟩
  | 5 => ⟨((-14044185791/137438953472), (-3974178259/68719476736)), (101/68719476736), by norm_num⟩
  | 6 => ⟨((12677453385/274877906944), (7174849489/274877906944)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-9808908625/549755813888), (-11102772915/1099511627776)), (287/1099511627776), by norm_num⟩
  | 8 => ⟨((13281508487/2199023255552), (3758358303/1099511627776)), (49/549755813888), by norm_num⟩
  | 9 => ⟨((-15985329657/8796093022208), (-9046953741/8796093022208)), (119/4398046511104), by norm_num⟩
  | 10 => ⟨((17315630077/35184372088832), (9799841959/35184372088832)), (65/8796093022208), by norm_num⟩
  | 11 => ⟨((-17051489277/140737488355328), (-9650350541/140737488355328)), (129/70368744177664), by norm_num⟩
  | 12 => ⟨((7696048161/281474976710656), (8711211241/562949953421312)), (235/562949953421312), by norm_num⟩
  | 13 => ⟨((-3206351503/562949953421312), (-7258583801/2251799813685248)), (99/1125899906842624), by norm_num⟩
  | 14 => ⟨((19846767617/18014398509481984), (1404043523/2251799813685248)), (309/18014398509481984), by norm_num⟩
  | 15 => ⟨((-14332278143/72057594037927936), (-4055701701/36028797018963968)), (225/72057594037927936), by norm_num⟩
  | 16 => ⟨((19406264353/576460752303423488), (10983043807/576460752303423488)), (307/576460752303423488), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (670856777365/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444591592522407/158456325028528675187087900672), (793582040933/633825300114114700748351602688)), (721/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889289269355377/39614081257132168796771975168), (446299411671/19807040628566084398385987584)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944518104957403/1237940039285380274899124224), (237040092353/618970019642690137449562112)), (6895/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770702632054435/154742504910672534362390528), (118488295367/19342813113834066795298816)), (13791/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774548028420569/4835703278458516698824704), (222098107041/2417851639229258349412352)), (6465/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258388669409025/604462909807314587353088), (194268423557/151115727451828646838272)), (5657/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943571182647075/37778931862957161709568), (157779916115/9444732965739290427392)), (4597/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((40532890421343/147573952589676412928), (59139842311/295147905179352825856)), (431/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1620779031428991/590295810358705651712), (650179336585/295147905179352825856)), (9483/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455659748212529/18446744073709551616), (812186148547/36893488147419103232)), (23711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227714725222151/1152921504606846976), (912970239133/4611686018427387904)), (26679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796483767309893/576460752303423488), (1824094339239/1152921504606846976)), (13343/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193691105666429/144115188075855872), (1594008120931/144115188075855872)), (23357/144115188075855872), by norm_num⟩
  | 4 => ⟨((186288208474701/4503599627370496), (2386869522899/36028797018963968)), (4381/4503599627370496), by norm_num⟩
  | 3 => ⟨((743798910117213/4503599627370496), (1488175582187/4503599627370496)), (43835/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224642742519355/4503599627370496), (5931050654547/4503599627370496)), (21935/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211181550460273/2251799813685248), (4421320354721/1125899906842624)), (8237/140737488355328), by norm_num⟩
  | 0 => ⟨((1085515563312153/1125899906842624), (17470699903257/2251799813685248)), (66079/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085515563312153/1125899906842624), (17470699903257/2251799813685248)), (252071382762718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2093023944123693/2251799813685248), (16844052061541/1125899906842624)), (256887/1125899906842624), by norm_num⟩
  | 2 => ⟨((1944939472726977/2251799813685248), (62625467977411/2251799813685248)), (970469/2251799813685248), by norm_num⟩
  | 3 => ⟨((1678154328091753/2251799813685248), (54091284636855/1125899906842624)), (1730421/2251799813685248), by norm_num⟩
  | 4 => ⟨((622723757137327/1125899906842624), (161246169173135/2251799813685248)), (2745463/2251799813685248), by norm_num⟩
  | 5 => ⟨((677297855018423/2251799813685248), (178367223731427/2251799813685248)), (428771/281474976710656), by norm_num⟩
  | 6 => ⟨((379178926400403/4503599627370496), (107298825858925/2251799813685248)), (5213741/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-21787939583/268435456)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile052Terms1

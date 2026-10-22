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
namespace Reinmann.XiBand97.Tile054Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨54,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15489/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15489/512))
  have he : value ((69/80), (15489/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-11257676227/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-322986056744069/1125899906842624), (-1056678646865573/2251799813685248)), (106045/35184372088832), by norm_num⟩
  | 1 => ⟨((6832180011/34359738368), (2794013309/8589934592)), (37/17179869184), by norm_num⟩
  | 2 => ⟨((-591963289/8589934592), (-15493299581/137438953472)), (105/137438953472), by norm_num⟩
  | 3 => ⟨((4376721971/274877906944), (7159424615/274877906944)), (99/549755813888), by norm_num⟩
  | 4 => ⟨((-12134849977/4398046511104), (-9925069973/2199023255552)), (35/1099511627776), by norm_num⟩
  | 5 => ⟨((6728989639/17592186044416), (5503627415/8796093022208)), (79/17592186044416), by norm_num⟩
  | 6 => ⟨((-12437813857/281474976710656), (-10172863535/140737488355328)), (37/70368744177664), by norm_num⟩
  | 7 => ⟨((4926420347/1125899906842624), (2014654765/281474976710656)), (119/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1707367187/4503599627370496), (-11171618161/18014398509481984)), (85/18014398509481984), by norm_num⟩
  | 9 => ⟨((4207846229/144115188075855872), (13766356677/288230376151711744)), (107/288230376151711744), by norm_num⟩
  | 10 => ⟨((-291665675/144115188075855872), (-3816844527/1152921504606846976)), (121/4611686018427387904), by norm_num⟩
  | 11 => ⟨((4704983047/36893488147419103232), (7696392793/36893488147419103232)), (31/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-4348327645/590295810358705651712), (-14225954573/1180591620717411303424)), (117/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((7419153347/18889465931478580854784), (1517027739/2361183241434822606848)), (51/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-11754434799/604462909807314587353088), (-1201741143/37778931862957161709568)), (41/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((8690723563/9671406556917033397649408), (7108125739/4835703278458516698824704)), (123/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-6023950535/154742504910672534362390528), (-19707909261/309485009821345068724781056)), (173/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-2760885516235/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445260677340569/158456325028528675187087900672), (-204707986769/39614081257132168796771975168)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892299432908285/39614081257132168796771975168), (-1842266635887/19807040628566084398385987584)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((946116815590521/1237940039285380274899124224), (-1957288118733/1237940039285380274899124224)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773899066316997/154742504910672534362390528), (-3914305734023/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48502864546451/302231454903657293676544), (-3669374132783/9671406556917033397649408)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315252194685063/151115727451828646838272), (-3210414780045/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((118212379877183/4722366482869645213696), (-1304096148859/18889465931478580854784)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650121279623259/2361183241434822606848), (-488977031773/590295810358705651712)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406290644945633/147573952589676412928), (-1344494916445/147573952589676412928)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((28564285029295/1152921504606846976), (-6721322407669/73786976294838206464)), (2979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456967925838011/2305843009213693952), (-1889975603707/2305843009213693952)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599114248339759/1152921504606846976), (-1889479804573/288230376151711744)), (3357/576460752303423488), by norm_num⟩
  | 5 => ⟨((299765349873835/36028797018963968), (-1652736512661/36028797018963968)), (2941/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498344961337077/36028797018963968), (-4955973564437/18014398509481984)), (2209/9007199254740992), by norm_num⟩
  | 3 => ⟨((1497618711376097/9007199254740992), (-12382095835509/9007199254740992)), (11069/9007199254740992), by norm_num⟩
  | 2 => ⟨((561149993676105/1125899906842624), (-773144652027/140737488355328)), (11105/2251799813685248), by norm_num⟩
  | 1 => ⟨((560226617163741/562949953421312), (-9262966668479/562949953421312)), (4187/281474976710656), by norm_num⟩
  | 0 => ⟨((557409977991725/562949953421312), (-36933206283489/1125899906842624)), (33861/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557409977991725/562949953421312), (-36933206283489/1125899906842624)), (129169468406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102637512435723/1125899906842624), (-36569747588621/562949953421312)), (34639/562949953421312), by norm_num⟩
  | 2 => ⟨((67194033563681/70368744177664), (-4476771787889/35184372088832)), (144695/1125899906842624), by norm_num⟩
  | 3 => ⟨((504186596571541/562949953421312), (-273587241983799/1125899906842624)), (313157/1125899906842624), by norm_num⟩
  | 4 => ⟨((418317166538739/562949953421312), (-490057844619707/1125899906842624)), (89141/140737488355328), by norm_num⟩
  | 5 => ⟨((408384718229623/1125899906842624), (-728304915048019/1125899906842624)), (840307/562949953421312), by norm_num⟩
  | 6 => ⟨((-322986056744069/1125899906842624), (-1056678646865573/2251799813685248)), (106045/35184372088832), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-11257676227/536870912)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-2230374333/67108864)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-429333952541801/4503599627370496), (-1692384898072783/4503599627370496)), (9181453/2251799813685248), by norm_num⟩
  | 1 => ⟨((3598568391/34359738368), (14185141343/34359738368)), (39/8589934592), by norm_num⟩
  | 2 => ⟨((-123544733/2147483648), (-3895992649/17179869184)), (173/68719476736), by norm_num⟩
  | 3 => ⟨((5791051173/274877906944), (11413827735/137438953472)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((-6362119983/1099511627776), (-6269685705/274877906944)), (71/274877906944), by norm_num⟩
  | 5 => ⟨((1397900639/1099511627776), (22041452037/4398046511104)), (63/1099511627776), by norm_num⟩
  | 6 => ⟨((-4095335521/17592186044416), (-16143340045/17592186044416)), (93/8796093022208), by norm_num⟩
  | 7 => ⟨((5141926777/140737488355328), (5067220501/35184372088832)), (59/35184372088832), by norm_num⟩
  | 8 => ⟨((-5648983945/1125899906842624), (-22267642847/1125899906842624)), (131/562949953421312), by norm_num⟩
  | 9 => ⟨((5516482827/9007199254740992), (10872669365/4503599627370496)), (129/4503599627370496), by norm_num⟩
  | 10 => ⟨((-4848380659/72057594037927936), (-2388969635/9007199254740992)), (229/72057594037927936), by norm_num⟩
  | 11 => ⟨((3873811325/576460752303423488), (7635058613/288230376151711744)), (185/576460752303423488), by norm_num⟩
  | 12 => ⟨((-5674422301/9223372036854775808), (-2795989739/1152921504606846976)), (137/4611686018427387904), by norm_num⟩
  | 13 => ⟨((1918150791/36893488147419103232), (3780564537/18446744073709551616)), (187/73786976294838206464), by norm_num⟩
  | 14 => ⟨((-4816694927/1180591620717411303424), (-18986855581/1180591620717411303424)), (237/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((705557365/2361183241434822606848), (11124902861/9444732965739290427392)), (35/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((-1550267983/75557863725914323419136), (-12221954993/151115727451828646838272)), (155/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-2369764421193/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890251973118269/316912650057057350374175801344), (-702427387923/158456325028528675187087900672)), (1445/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((29557710348019/618970019642690137449562112), (-1580323873599/19807040628566084398385987584)), (813/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((14778046485567/19342813113834066795298816), (-839465644119/618970019642690137449562112)), (27/9671406556917033397649408), by norm_num⟩
  | 14 => ⟨((1773255568432245/154742504910672534362390528), (-1678748092433/77371252455336267181195264)), (6913/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551488580817401/9671406556917033397649408), (-196703960613/604462909807314587353088)), (6483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315120318565367/151115727451828646838272), (-2753466131107/604462909807314587353088)), (2837/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890541248162719/75557863725914323419136), (-1118413115791/18889465931478580854784)), (9223/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324900064038319/1180591620717411303424), (-3354600567933/4722366482869645213696)), (865/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624279931943757/590295810358705651712), (-2305768854547/295147905179352825856)), (9519/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456752927626891/18446744073709551616), (-2881432466171/36893488147419103232)), (93/576460752303423488), by norm_num⟩
  | 7 => ⟨((456658106500679/2305843009213693952), (-1620270434369/2305843009213693952)), (1675/1152921504606846976), by norm_num⟩
  | 6 => ⟨((798938154591029/576460752303423488), (-6478404865501/1152921504606846976)), (13411/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197979708392769/144115188075855872), (-1416398114533/36028797018963968)), (11747/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496725436485783/36028797018963968), (-8492364298641/36028797018963968)), (17643/36028797018963968), by norm_num⟩
  | 3 => ⟨((186949947129453/1125899906842624), (-10604910930007/9007199254740992)), (22095/9007199254740992), by norm_num⟩
  | 2 => ⟨((70018047668671/140737488355328), (-5294545387483/1125899906842624)), (11079/1125899906842624), by norm_num⟩
  | 1 => ⟨((558728089377373/562949953421312), (-15844073723701/1125899906842624)), (2087/70368744177664), by norm_num⟩
  | 0 => ⟨((1108905012286607/1125899906842624), (-31529826697369/1125899906842624)), (67411/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108905012286607/1125899906842624), (-31529826697369/1125899906842624)), (257152561668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((68205230147211/70368744177664), (-31053899772751/562949953421312)), (136563/1125899906842624), by norm_num⟩
  | 2 => ⟨((1054305706392289/1125899906842624), (-120396542852683/1125899906842624)), (69949/281474976710656), by norm_num⟩
  | 3 => ⟨((974389631203523/1125899906842624), (-112740716459825/562949953421312)), (583849/1125899906842624), by norm_num⟩
  | 4 => ⟨((199527789136553/281474976710656), (-97569406006057/281474976710656)), (4861/4398046511104), by norm_num⟩
  | 5 => ⟨((860937622330367/2251799813685248), (-1106616756928547/2251799813685248)), (1313483/562949953421312), by norm_num⟩
  | 6 => ⟨((-429333952541801/4503599627370496), (-1692384898072783/4503599627370496)), (9181453/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-2230374333/67108864)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-11257676227/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-77636762722807/562949953421312), (1212514424497527/4503599627370496)), (14941279/4503599627370496), by norm_num⟩
  | 1 => ⟨((6569055565/34359738368), (-3206065959/8589934592)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((-569165293/4294967296), (8889102321/34359738368)), (7/2147483648), by norm_num⟩
  | 3 => ⟨((8416326787/137438953472), (-8215274949/68719476736)), (209/137438953472), by norm_num⟩
  | 4 => ⟨((-5833753183/274877906944), (11388789337/274877906944)), (73/137438953472), by norm_num⟩
  | 5 => ⟨((3234919657/549755813888), (-12630571551/1099511627776)), (41/274877906944), by norm_num⟩
  | 6 => ⟨((-1494850293/1099511627776), (5836563373/2199023255552)), (153/4398046511104), by norm_num⟩
  | 7 => ⟨((9473383003/35184372088832), (-9247079877/17592186044416)), (61/8796093022208), by norm_num⟩
  | 8 => ⟨((-6566448719/140737488355328), (12819174691/140737488355328)), (171/140737488355328), by norm_num⟩
  | 9 => ⟨((4045791481/562949953421312), (-3949144353/281474976710656)), (213/1125899906842624), by norm_num⟩
  | 10 => ⟨((-4486926333/4503599627370496), (17518964953/9007199254740992)), (239/9007199254740992), by norm_num⟩
  | 11 => ⟨((9047564617/72057594037927936), (-17662867147/72057594037927936)), (243/72057594037927936), by norm_num⟩
  | 12 => ⟨((-8361725207/576460752303423488), (8161977709/288230376151711744)), (227/576460752303423488), by norm_num⟩
  | 13 => ⟨((7133423079/4611686018427387904), (-13926035291/4611686018427387904)), (49/1152921504606846976), by norm_num⟩
  | 14 => ⟨((-2825435483/18446744073709551616), (22063524797/73786976294838206464)), (313/73786976294838206464), by norm_num⟩
  | 15 => ⟨((4178010963/295147905179352825856), (-4078205335/147573952589676412928)), (233/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-5791953039/4722366482869645213696), (11307186119/4722366482869645213696)), (325/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (332847418927/1267650600228229401496703205376)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890059851751421/316912650057057350374175801344), (197239503981/39614081257132168796771975168)), (5783/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891261168249969/39614081257132168796771975168), (1774961350313/19807040628566084398385987584)), (6507/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891130606631829/2475880078570760549798248448), (1885665706973/1237940039285380274899124224)), (6915/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772796189957817/154742504910672534362390528), (1885406124043/77371252455336267181195264)), (1729/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551057876413481/9671406556917033397649408), (441823109035/1208925819614629174706176)), (3243/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157513046360597/75557863725914323419136), (3092210156769/604462909807314587353088)), (5677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944964355443151/37778931862957161709568), (5023807250851/75557863725914323419136)), (2307/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162392599087139/590295810358705651712), (1883475237173/2361183241434822606848)), (1731/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623648071623189/590295810358705651712), (647260794003/73786976294838206464)), (9525/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114138858651759/4611686018427387904), (1617600535799/18446744073709551616)), (1489/9223372036854775808), by norm_num⟩
  | 7 => ⟨((7131810571947/36028797018963968), (7276169487717/9223372036854775808)), (13411/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596987139385855/1152921504606846976), (3636189203079/576460752303423488)), (13423/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197201404750231/144115188075855872), (1589766560351/36028797018963968)), (11759/144115188075855872), by norm_num⟩
  | 4 => ⟨((186944678052599/4503599627370496), (4765034949813/18014398509481984)), (69/140737488355328), by norm_num⟩
  | 3 => ⟨((1494138595859355/9007199254740992), (1487207679509/1125899906842624)), (11063/4503599627370496), by norm_num⟩
  | 2 => ⟨((139853293533883/281474976710656), (11875273828877/2251799813685248)), (22197/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115259029500455/1125899906842624), (17756946540919/1125899906842624)), (33471/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104496935594277/1125899906842624), (2205629204509/70368744177664)), (67645/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104496935594277/1125899906842624), (2205629204509/70368744177664)), (258045200828170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082394699993007/1125899906842624), (34619215191433/562949953421312)), (535/4398046511104), by norm_num⟩
  | 2 => ⟨((259078164772901/281474976710656), (133126061431897/1125899906842624)), (140091/562949953421312), by norm_num⟩
  | 3 => ⟨((469056517698415/562949953421312), (122533292594157/562949953421312)), (291017/562949953421312), by norm_num⟩
  | 4 => ⟨((364152457524011/562949953421312), (408384718229629/1125899906842624)), (1223291/1125899906842624), by norm_num⟩
  | 5 => ⟨((645972113488137/2251799813685248), (1056678646865593/2251799813685248)), (4940057/2251799813685248), by norm_num⟩
  | 6 => ⟨((-77636762722807/562949953421312), (1212514424497527/4503599627370496)), (14941279/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-11257676227/268435456)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-26139514713/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-6794424361935/4503599627370496), (561901527560305/2251799813685248)), (5598361/2251799813685248), by norm_num⟩
  | 1 => ⟨((83428987/34359738368), (-6899609539/17179869184)), (277/68719476736), by norm_num⟩
  | 2 => ⟨((-134273775/68719476736), (11104493173/34359738368)), (225/68719476736), by norm_num⟩
  | 3 => ⟨((144070203/137438953472), (-23829323081/137438953472)), (243/137438953472), by norm_num⟩
  | 4 => ⟨((-115936023/274877906944), (19175907997/274877906944)), (197/274877906944), by norm_num⟩
  | 5 => ⟨((149273465/1099511627776), (-6172486667/274877906944)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-160164249/4398046511104), (26491290815/4398046511104)), (277/4398046511104), by norm_num⟩
  | 7 => ⟨((147299665/17592186044416), (-24363478735/17592186044416)), (257/17592186044416), by norm_num⟩
  | 8 => ⟨((-118534833/70368744177664), (19605753177/70368744177664)), (209/70368744177664), by norm_num⟩
  | 9 => ⟨((169577293/562949953421312), (-7012053881/140737488355328)), (301/562949953421312), by norm_num⟩
  | 10 => ⟨((-54584825/1125899906842624), (141068317/17592186044416)), (195/2251799813685248), by norm_num⟩
  | 11 => ⟨((31945777/4503599627370496), (-10567712471/9007199254740992)), (115/9007199254740992), by norm_num⟩
  | 12 => ⟨((-68552993/72057594037927936), (22677436131/144115188075855872)), (31/18014398509481984), by norm_num⟩
  | 13 => ⟨((135792967/1152921504606846976), (-22460261825/1152921504606846976)), (247/1152921504606846976), by norm_num⟩
  | 14 => ⟨((-62442957/4611686018427387904), (10328113401/4611686018427387904)), (229/9223372036854775808), by norm_num⟩
  | 15 => ⟨((107197933/73786976294838206464), (-17730621089/73786976294838206464)), (99/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-86264209/590295810358705651712), (28536333791/1180591620717411303424)), (321/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (2054012986999/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779824779745187/633825300114114700748351602688), (19012277803/4951760157141521099596496896)), (2889/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945464773073009/19807040628566084398385987584), (1368713201441/19807040628566084398385987584)), (3251/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472694615998479/618970019642690137449562112), (45439110181/38685626227668133590597632)), (6909/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221555534855869/19342813113834066795298816), (2907639032223/154742504910672534362390528)), (3455/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550728205679871/9671406556917033397649408), (681354658045/2417851639229258349412352)), (405/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259816154853003/604462909807314587353088), (74507762817/18889465931478580854784)), (5671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889460820667953/75557863725914323419136), (484184954447/9444732965739290427392)), (4609/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298790278107985/4722366482869645213696), (1452150671575/2361183241434822606848)), (6915/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202895846096217/73786976294838206464), (3992100992727/590295810358705651712)), (1189/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912810545707115/36893488147419103232), (1247039170209/18446744073709551616)), (11895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825069127339067/9223372036854775808), (5608968886531/9223372036854775808)), (13389/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199539305635565/144115188075855872), (2802792905559/576460752303423488)), (6699/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196614690911995/144115188075855872), (612635400633/18014398509481984)), (5867/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494681136763955/36028797018963968), (7344020000227/36028797018963968)), (17621/36028797018963968), by norm_num⟩
  | 3 => ⟨((373262461787241/2251799813685248), (2291681370865/2251799813685248)), (22063/9007199254740992), by norm_num⟩
  | 2 => ⟨((558873748358163/1125899906842624), (2286698502685/562949953421312)), (5529/562949953421312), by norm_num⟩
  | 1 => ⟨((556832714031211/562949953421312), (13670424689519/1125899906842624)), (16655/562949953421312), by norm_num⟩
  | 0 => ⟨((550704017078317/562949953421312), (6785539643179/281474976710656)), (16791/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550704017078317/562949953421312), (6785539643179/281474976710656)), (64052582860851199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((538397309372127/562949953421312), (13275865525283/281474976710656)), (134645/1125899906842624), by norm_num⟩
  | 2 => ⟨((1027326377984267/1125899906842624), (3174212127987/35184372088832)), (33781/140737488355328), by norm_num⟩
  | 3 => ⟨((928219323026989/1125899906842624), (370727303606897/2251799813685248)), (1083875/2251799813685248), by norm_num⟩
  | 4 => ⟨((1469458205304569/2251799813685248), (305636624259633/1125899906842624)), (2144037/2251799813685248), by norm_num⟩
  | 5 => ⟨((792988977940835/2251799813685248), (398898909779095/1125899906842624)), (495289/281474976710656), by norm_num⟩
  | 6 => ⟨((-6794424361935/4503599627370496), (561901527560305/2251799813685248)), (5598361/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-26139514713/536870912)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-29100670891/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-83875640907247/562949953421312), (85870281251593/562949953421312)), (10826359/4503599627370496), by norm_num⟩
  | 1 => ⟨((2293166715/8589934592), (-9390801365/34359738368)), (149/34359738368), by norm_num⟩
  | 2 => ⟨((-16435212705/68719476736), (8413028635/34359738368)), (269/68719476736), by norm_num⟩
  | 3 => ⟨((1226997833/8589934592), (-10049415815/68719476736)), (163/68719476736), by norm_num⟩
  | 4 => ⟨((-1099242493/17179869184), (4501533987/68719476736)), (37/34359738368), by norm_num⟩
  | 5 => ⟨((12605300133/549755813888), (-3226266459/137438953472)), (107/274877906944), by norm_num⟩
  | 6 => ⟨((-1882138823/274877906944), (15415182609/2199023255552)), (129/1099511627776), by norm_num⟩
  | 7 => ⟨((963525731/549755813888), (-7891514117/4398046511104)), (133/4398046511104), by norm_num⟩
  | 8 => ⟨((-13811250819/35184372088832), (7069847573/17592186044416)), (15/2199023255552), by norm_num⟩
  | 9 => ⟨((1374802191/17592186044416), (-2814992519/35184372088832)), (193/140737488355328), by norm_num⟩
  | 10 => ⟨((-7882607501/562949953421312), (8070063203/562949953421312)), (279/1125899906842624), by norm_num⟩
  | 11 => ⟨((2567952115/1125899906842624), (-2629020393/1125899906842624)), (183/4503599627370496), by norm_num⟩
  | 12 => ⟨((-6134870025/18014398509481984), (196273841/562949953421312)), (55/9007199254740992), by norm_num⟩
  | 13 => ⟨((13528875643/288230376151711744), (-13850604827/288230376151711744)), (61/72057594037927936), by norm_num⟩
  | 14 => ⟨((-13851709167/2305843009213693952), (14181115631/2305843009213693952)), (63/576460752303423488), by norm_num⟩
  | 15 => ⟨((13236763235/18446744073709551616), (-13551545715/18446744073709551616)), (243/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-5929273967/73786976294838206464), (12140555179/147573952589676412928)), (219/147573952589676412928), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (3053900446457/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779578291615063/633825300114114700748351602688), (3617289055603/633825300114114700748351602688)), (2893/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472663015474275/9903520314283042199192993792), (1017219734639/9903520314283042199192993792)), (3255/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236310424814329/309485009821345068724781056), (4322500406215/2475880078570760549798248448)), (6919/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886074472629469/77371252455336267181195264), (1080432873373/38685626227668133590597632)), (6921/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387612761434399/2417851639229258349412352), (4050806351901/9671406556917033397649408)), (3245/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259573355382155/604462909807314587353088), (442954835861/75557863725914323419136)), (5681/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889065738437259/75557863725914323419136), (5756881344183/75557863725914323419136)), (4617/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649246750183791/2361183241434822606848), (2158160518875/2361183241434822606848)), (6929/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622757942742313/590295810358705651712), (2966382092149/295147905179352825856)), (9533/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825108925196875/73786976294838206464), (1853172433395/18446744073709551616)), (2981/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824491383590677/9223372036854775808), (4167393245217/4611686018427387904)), (13425/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797867379241369/576460752303423488), (8329175565933/1152921504606846976)), (6719/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196105283670051/144115188075855872), (7281717572803/144115188075855872)), (5887/72057594037927936), by norm_num⟩
  | 4 => ⟨((746956336787065/18014398509481984), (2727489346343/9007199254740992)), (4423/9007199254740992), by norm_num⟩
  | 3 => ⟨((186510209428337/1125899906842624), (6807685294381/4503599627370496)), (2771/1125899906842624), by norm_num⟩
  | 2 => ⟨((558383991755879/1125899906842624), (13582270594455/2251799813685248)), (22249/2251799813685248), by norm_num⟩
  | 1 => ⟨((556083985488465/562949953421312), (5072676528609/281474976710656)), (33575/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098301367481843/1125899906842624), (10062729466007/281474976710656)), (8495/140737488355328), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098301367481843/1125899906842624), (10062729466007/281474976710656)), (32405853808355287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((33435636410217/35184372088832), (78528540350329/1125899906842624)), (17181/140737488355328), by norm_num⟩
  | 2 => ⟨((252821242447615/281474976710656), (74625510335939/562949953421312)), (280407/1125899906842624), by norm_num⟩
  | 3 => ⟨((888552718472097/1125899906842624), (268114977208987/1125899906842624)), (578067/1125899906842624), by norm_num⟩
  | 4 => ⟨((1274785241812243/2251799813685248), (846378227457939/2251799813685248)), (2375457/2251799813685248), by norm_num⟩
  | 5 => ⟨((100888332002775/562949953421312), (958300526358779/2251799813685248)), (4475295/2251799813685248), by norm_num⟩
  | 6 => ⟨((-83875640907247/562949953421312), (85870281251593/562949953421312)), (10826359/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-29100670891/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-15802146383/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-571923871381969/4503599627370496), (-616238673592423/4503599627370496)), (4746531/2251799813685248), by norm_num⟩
  | 1 => ⟨((8490848281/34359738368), (4574375493/17179869184)), (143/34359738368), by norm_num⟩
  | 2 => ⟨((-4130606961/17179869184), (-17802647395/68719476736)), (35/8589934592), by norm_num⟩
  | 3 => ⟨((10717053343/68719476736), (11547450749/68719476736)), (183/68719476736), by norm_num⟩
  | 4 => ⟨((-5213605717/68719476736), (-2808787701/34359738368)), (45/34359738368), by norm_num⟩
  | 5 => ⟨((16232333245/549755813888), (17490075181/549755813888)), (141/274877906944), by norm_num⟩
  | 6 => ⟨((-10528887335/1099511627776), (-5672352467/549755813888)), (23/137438953472), by norm_num⟩
  | 7 => ⟨((731723883/274877906944), (12614729411/4398046511104)), (103/2199023255552), by norm_num⟩
  | 8 => ⟨((-5695475721/8796093022208), (-6136782497/8796093022208)), (101/8796093022208), by norm_num⟩
  | 9 => ⟨((9851452453/70368744177664), (10614779861/70368744177664)), (11/4398046511104), by norm_num⟩
  | 10 => ⟨((-15336033049/562949953421312), (-16524326289/562949953421312)), (69/140737488355328), by norm_num⟩
  | 11 => ⟨((678239599/140737488355328), (5846337133/1125899906842624)), (197/2251799813685248), by norm_num⟩
  | 12 => ⟨((-14077795405/18014398509481984), (-15168595683/18014398509481984)), (257/18014398509481984), by norm_num⟩
  | 13 => ⟨((8428961525/72057594037927936), (9082069011/72057594037927936)), (39/18014398509481984), by norm_num⟩
  | 14 => ⟨((-2343143111/144115188075855872), (-2524698609/144115188075855872)), (175/576460752303423488), by norm_num⟩
  | 15 => ⟨((4863515691/2305843009213693952), (10480718179/4611686018427387904)), (183/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-9463964543/36893488147419103232), (-10197267937/36893488147419103232)), (45/9223372036854775808), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-3020645501419/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444843331682865/158456325028528675187087900672), (-447139348639/79228162514264337593543950336)), (5785/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890421520635929/39614081257132168796771975168), (-4023644131723/39614081257132168796771975168)), (3255/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472559625050935/618970019642690137449562112), (-4274388149885/2475880078570760549798248448)), (6919/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885952052608851/77371252455336267181195264), (-4273562715905/154742504910672534362390528)), (865/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775110785058249/4835703278458516698824704), (-500698513251/1208925819614629174706176)), (3245/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259372626138089/604462909807314587353088), (-1752006373169/302231454903657293676544)), (355/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944369834769183/37778931862957161709568), (-5692376825113/75557863725914323419136)), (4617/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298249050315209/4722366482869645213696), (-4267844416645/4722366482869645213696)), (6929/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622421989082647/590295810358705651712), (-5865949368853/590295810358705651712)), (2383/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824689230912719/73786976294838206464), (-916116538903/9223372036854775808)), (11923/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824019568308635/9223372036854775808), (-8240231368159/9223372036854775808)), (839/576460752303423488), by norm_num⟩
  | 6 => ⟨((1595263369298209/1152921504606846976), (-2058552780001/288230376151711744)), (13437/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195693297647439/144115188075855872), (-7198164160941/144115188075855872)), (11773/144115188075855872), by norm_num⟩
  | 4 => ⟨((746647826974871/18014398509481984), (-2695927660277/9007199254740992)), (17689/36028797018963968), by norm_num⟩
  | 3 => ⟨((23301751261129/140737488355328), (-13455963495375/9007199254740992)), (5541/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116000910195819/2251799813685248), (-13420476361213/2251799813685248)), (22245/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111023670250689/1125899906842624), (-10021042426615/562949953421312)), (16783/562949953421312), by norm_num⟩
  | 0 => ⟨((274009509164567/281474976710656), (-9932545724629/281474976710656)), (33967/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274009509164567/281474976710656), (-9932545724629/281474976710656)), (129573824168968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((133195775561097/140737488355328), (-38676432421315/562949953421312)), (34265/281474976710656), by norm_num⟩
  | 2 => ⟨((501575612354645/562949953421312), (-146415499452059/1125899906842624)), (278265/1125899906842624), by norm_num⟩
  | 3 => ⟨((874744615547443/1125899906842624), (-65226440955859/281474976710656)), (284115/562949953421312), by norm_num⟩
  | 4 => ⟨((1238309587906189/2251799813685248), (-810821319667253/2251799813685248)), (2292605/2251799813685248), by norm_num⟩
  | 5 => ⟨((194506504918801/1125899906842624), (-445886800469845/1125899906842624)), (260783/140737488355328), by norm_num⟩
  | 6 => ⟨((-571923871381969/4503599627370496), (-616238673592423/4503599627370496)), (4746531/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-15802146383/268435456)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-481443911/268435456), (-4221628585/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1494313622253665/9007199254740992), (-112757471812561/9007199254740992)), (12359481/9007199254740992), by norm_num⟩
  | 1 => ⟨((-23707106189/68719476736), (1788883751/68719476736)), (99/34359738368), by norm_num⟩
  | 2 => ⟨((24648770721/68719476736), (-1859939593/68719476736)), (209/68719476736), by norm_num⟩
  | 3 => ⟨((-8542612965/34359738368), (1289211885/68719476736)), (147/68719476736), by norm_num⟩
  | 4 => ⟨((8881932137/68719476736), (-1340420375/137438953472)), (155/137438953472), by norm_num⟩
  | 5 => ⟨((-14775566925/274877906944), (2229860649/549755813888)), (65/137438953472), by norm_num⟩
  | 6 => ⟨((20483285111/1099511627776), (-772810811/549755813888)), (91/549755813888), by norm_num⟩
  | 7 => ⟨((-3042413855/549755813888), (918294231/2199023255552)), (109/2199023255552), by norm_num⟩
  | 8 => ⟨((6326521757/4398046511104), (-1909539171/17592186044416)), (115/8796093022208), by norm_num⟩
  | 9 => ⟨((-23387790499/70368744177664), (1764788923/70368744177664)), (215/70368744177664), by norm_num⟩
  | 10 => ⟨((19453417253/281474976710656), (-91744385/17592186044416)), (181/281474976710656), by norm_num⟩
  | 11 => ⟨((-919369181/70368744177664), (2219951539/2251799813685248)), (69/562949953421312), by norm_num⟩
  | 12 => ⟨((20392260983/9007199254740992), (-769376575/4503599627370496)), (97/4503599627370496), by norm_num⟩
  | 13 => ⟨((-13047542959/36028797018963968), (984537607/36028797018963968)), (251/72057594037927936), by norm_num⟩
  | 14 => ⟨((15503773055/288230376151711744), (-2339758171/576460752303423488)), (301/576460752303423488), by norm_num⟩
  | 15 => ⟨((-8597117265/1152921504606846976), (81089839/144115188075855872)), (169/2305843009213693952), by norm_num⟩
  | 16 => ⟨((4469300695/4611686018427387904), (-1348972639/18446744073709551616)), (89/9223372036854775808), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395409877308005/2535301200456458802993406410752), (-12263270299/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444800629117151/158456325028528675187087900672), (-29039351335/158456325028528675187087900672)), (11527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890229783067307/39614081257132168796771975168), (-130656504449/39614081257132168796771975168)), (1621/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890035319659227/2475880078570760549798248448), (-8674821279/154742504910672534362390528)), (13779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442925383131851/38685626227668133590597632), (-34692144885/38685626227668133590597632)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775016151871299/4835703278458516698824704), (-130065205655/9671406556917033397649408)), (6459/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314801915805549/151115727451828646838272), (-28444181661/151115727451828646838272)), (11303/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944236406854235/37778931862957161709568), (-184830335107/75557863725914323419136)), (287/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324512491367255/1180591620717411303424), (-69286515613/2361183241434822606848)), (13777/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6336523295493/2305843009213693952), (-47614290003/147573952589676412928)), (9471/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456087942734523/18446744073709551616), (-237950378273/73786976294838206464)), (23679/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823643457998893/9223372036854775808), (-133763903853/4611686018427387904)), (26639/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594891668056775/1152921504606846976), (-267320006471/1152921504606846976)), (26639/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597686505417959/72057594037927936), (-233671447133/144115188075855872)), (11655/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492825106234859/36028797018963968), (-350040597739/36028797018963968)), (4371/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490741143148911/9007199254740992), (-436735467193/9007199254740992)), (21857/4503599627370496), by norm_num⟩
  | 2 => ⟨((2230911497594721/4503599627370496), (-217757494411/1125899906842624)), (87437/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220540077223093/2251799813685248), (-1300459631705/2251799813685248)), (8199/140737488355328), by norm_num⟩
  | 0 => ⟨((2189570481230795/2251799813685248), (-2576679994497/2251799813685248)), (32811/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189570481230795/2251799813685248), (-2576679994497/2251799813685248)), (125164033056163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2129057931287131/2251799813685248), (-1252736238195/562949953421312)), (511069/2251799813685248), by norm_num⟩
  | 2 => ⟨((1006497677470923/1125899906842624), (-4737806633663/1125899906842624)), (968699/2251799813685248), by norm_num⟩
  | 3 => ⟨((1799476350936871/2251799813685248), (-4235359949945/562949953421312)), (870045/1125899906842624), by norm_num⟩
  | 4 => ⟨((718942266874875/1125899906842624), (-27076758853295/2251799813685248)), (1403647/1125899906842624), by norm_num⟩
  | 5 => ⟨((1835668312046167/4503599627370496), (-34579674927237/2251799813685248)), (7305405/4503599627370496), by norm_num⟩
  | 6 => ⟨((1494313622253665/9007199254740992), (-112757471812561/9007199254740992)), (12359481/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-481443911/268435456), (-4221628585/67108864)), (1/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile054Terms0

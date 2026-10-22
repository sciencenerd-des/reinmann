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
namespace Reinmann.XiBand97.Tile052Terms0
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
  | 0 => ⟨((-320962607/536870912), (-11153595961/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-430299327072229/2251799813685248), (-1161332090001413/2251799813685248)), (6609587/2251799813685248), by norm_num⟩
  | 1 => ⟨((9102196209/68719476736), (24565858883/68719476736)), (143/68719476736), by norm_num⟩
  | 2 => ⟨((-6309161639/137438953472), (-17027755823/137438953472)), (101/137438953472), by norm_num⟩
  | 3 => ⟨((5830903469/549755813888), (983561745/34359738368)), (95/549755813888), by norm_num⟩
  | 4 => ⟨((-8083348599/4398046511104), (-21816097615/4398046511104)), (67/2199023255552), by norm_num⟩
  | 5 => ⟨((4482360233/17592186044416), (24194826485/35184372088832)), (151/35184372088832), by norm_num⟩
  | 6 => ⟨((-4142580477/140737488355328), (-22360767683/281474976710656)), (71/140737488355328), by norm_num⟩
  | 7 => ⟨((1640810273/562949953421312), (4428372307/562949953421312)), (115/2251799813685248), by norm_num⟩
  | 8 => ⟨((-9098584117/36028797018963968), (-24556110233/36028797018963968)), (81/18014398509481984), by norm_num⟩
  | 9 => ⟨((2802959079/144115188075855872), (7564888255/144115188075855872)), (101/288230376151711744), by norm_num⟩
  | 10 => ⟨((-6217162185/4611686018427387904), (-16779459089/4611686018427387904)), (57/2305843009213693952), by norm_num⟩
  | 11 => ⟨((3134115229/36893488147419103232), (8458643461/36893488147419103232)), (117/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-2896537513/590295810358705651712), (-15634892977/1180591620717411303424)), (55/590295810358705651712), by norm_num⟩
  | 13 => ⟨((1235524191/4722366482869645213696), (13338193213/18889465931478580854784)), (3/590295810358705651712), by norm_num⟩
  | 14 => ⟨((-3914971929/302231454903657293676544), (-21132185187/604462909807314587353088)), (155/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((5789123743/9671406556917033397649408), (15624228887/9671406556917033397649408)), (29/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-8025429601/309485009821345068724781056), (-21659780403/309485009821345068724781056)), (163/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-2508355226259/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55657615841865/19807040628566084398385987584), (-1487871468627/316912650057057350374175801344)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892300615784213/39614081257132168796771975168), (-1673760721607/19807040628566084398385987584)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892234961801497/2475880078570760549798248448), (-1778261692561/1237940039285380274899124224)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886950239985427/77371252455336267181195264), (-3556277901485/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776046539496775/4835703278458516698824704), (-1666874824109/4835703278458516698824704)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315252525936803/151115727451828646838272), (-2916769992479/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891400396485063/75557863725914323419136), (-4739261818399/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300244442694583/4722366482869645213696), (-3554017983243/4722366482869645213696)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625165404442207/590295810358705651712), (-4886078348841/590295810358705651712)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828118124948771/73786976294838206464), (-1526638228671/18446744073709551616)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827876555943837/9223372036854775808), (-1717108596791/2305843009213693952)), (6703/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799559852892323/576460752303423488), (-6866636229655/1152921504606846976)), (6709/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199066854787113/144115188075855872), (-6006282255775/144115188075855872)), (1469/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498354503247641/36028797018963968), (-4502685351681/18014398509481984)), (8827/36028797018963968), by norm_num⟩
  | 3 => ⟨((187204126816007/1125899906842624), (-11249612674987/9007199254740992)), (11055/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122317849261849/2251799813685248), (-11238944625551/2251799813685248)), (11089/2251799813685248), by norm_num⟩
  | 1 => ⟨((140061113366513/140737488355328), (-8415843746531/562949953421312)), (16715/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114926716860679/1125899906842624), (-33556102508885/1125899906842624)), (1055/35184372088832), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114926716860679/1125899906842624), (-33556102508885/1125899906842624)), (4024505749452103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((275765093416901/281474976710656), (-66458119364781/1125899906842624)), (68875/1125899906842624), by norm_num⟩
  | 2 => ⟨((134595169046371/140737488355328), (-65109977835719/562949953421312)), (8943/70368744177664), by norm_num⟩
  | 3 => ⟨((1014706339490243/1125899906842624), (-249073322987785/1125899906842624)), (153393/562949953421312), by norm_num⟩
  | 4 => ⟨((429696915905669/562949953421312), (-224474909623501/562949953421312)), (86089/140737488355328), by norm_num⟩
  | 5 => ⟨((476953426045997/1125899906842624), (-685362354342247/1125899906842624)), (800313/562949953421312), by norm_num⟩
  | 6 => ⟨((-430299327072229/2251799813685248), (-1161332090001413/2251799813685248)), (6609587/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-11153595961/536870912)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-8839015673/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((12830786769621/562949953421312), (-217871737795643/562949953421312)), (8467677/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1720710451/68719476736), (29218331115/68719476736)), (287/68719476736), by norm_num⟩
  | 2 => ⟨((1890393647/137438953472), (-32099617617/137438953472)), (159/68719476736), by norm_num⟩
  | 3 => ⟨((-692269897/137438953472), (23510022917/274877906944)), (235/274877906944), by norm_num⟩
  | 4 => ⟨((95067027/68719476736), (-25828400083/1099511627776)), (65/274877906944), by norm_num⟩
  | 5 => ⟨((-1336855093/4398046511104), (11350159091/2199023255552)), (231/4398046511104), by norm_num⟩
  | 6 => ⟨((489561811/8796093022208), (-16625899007/17592186044416)), (171/17592186044416), by norm_num⟩
  | 7 => ⟨((-1229345421/140737488355328), (20874762239/140737488355328)), (217/140737488355328), by norm_num⟩
  | 8 => ⟨((1350573987/1125899906842624), (-11466635159/562949953421312)), (241/1125899906842624), by norm_num⟩
  | 9 => ⟨((-659447635/4503599627370496), (11197676707/4503599627370496)), (119/4503599627370496), by norm_num⟩
  | 10 => ⟨((1159163641/72057594037927936), (-19683048375/72057594037927936)), (211/72057594037927936), by norm_num⟩
  | 11 => ⟨((-926161033/576460752303423488), (31453147379/1152921504606846976)), (85/288230376151711744), by norm_num⟩
  | 12 => ⟨((84790991/576460752303423488), (-11518271409/4611686018427387904)), (251/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-1834386209/147573952589676412928), (31148589573/147573952589676412928)), (171/73786976294838206464), by norm_num⟩
  | 14 => ⟨((287897033/295147905179352825856), (-9777206651/590295810358705651712)), (217/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((-337373033/4722366482869645213696), (22914900001/18889465931478580854784)), (257/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((23165135/4722366482869645213696), (-12587295367/151115727451828646838272)), (285/302231454903657293676544), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-1969513382923/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111281578019285/39614081257132168796771975168), (-1167576092099/316912650057057350374175801344)), (2889/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891695004869145/39614081257132168796771975168), (-328352395345/4951760157141521099596496896)), (6501/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945795842673413/1237940039285380274899124224), (-2790724941531/2475880078570760549798248448)), (1727/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886628705903927/77371252455336267181195264), (-697605179295/38685626227668133590597632)), (6909/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775745211945585/4835703278458516698824704), (-2615696191327/9671406556917033397649408)), (6479/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260483001822421/604462909807314587353088), (-2288410944637/604462909807314587353088)), (2835/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890544270752971/75557863725914323419136), (-3718061759913/75557863725914323419136)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((324900677851631/1180591620717411303424), (-2788016065569/4722366482869645213696)), (3457/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624283613771289/590295810358705651712), (-239541278745/36893488147419103232)), (4755/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827016771310353/73786976294838206464), (-1197383296911/18446744073709551616)), (11893/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826638749441075/9223372036854775808), (-1346611974583/2305843009213693952)), (6693/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597883419523119/1152921504606846976), (-1346056717177/288230376151711744)), (13395/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598993407162451/72057594037927936), (-4708700048697/144115188075855872)), (11731/144115188075855872), by norm_num⟩
  | 4 => ⟨((748368930973385/18014398509481984), (-1764513411249/9007199254740992)), (17615/36028797018963968), by norm_num⟩
  | 3 => ⟨((747809097693117/4503599627370496), (-4406912213715/4503599627370496)), (22053/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120312000914687/2251799813685248), (-8800712742165/2251799813685248)), (22105/2251799813685248), by norm_num⟩
  | 1 => ⟨((558751275508443/562949953421312), (-13168297881207/1125899906842624)), (33287/1125899906842624), by norm_num⟩
  | 0 => ⟨((554521804103611/562949953421312), (-6551389836483/281474976710656)), (33547/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554521804103611/562949953421312), (-6551389836483/281474976710656)), (127971651317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1091829732015857/1125899906842624), (-1613326588551/35184372088832)), (135303/1125899906842624), by norm_num⟩
  | 2 => ⟨((528211640332961/562949953421312), (-25032107044349/281474976710656)), (137413/562949953421312), by norm_num⟩
  | 3 => ⟨((982329280855219/1125899906842624), (-46974869586641/281474976710656)), (564617/1125899906842624), by norm_num⟩
  | 4 => ⟨((206427009277781/281474976710656), (-163939226138555/562949953421312)), (1173695/1125899906842624), by norm_num⟩
  | 5 => ⟨((1020143051068829/2251799813685248), (-120229103668719/281474976710656)), (1202557/562949953421312), by norm_num⟩
  | 6 => ⟨((12830786769621/562949953421312), (-217871737795643/562949953421312)), (8467677/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-8839015673/268435456)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-320962607/268435456), (-11153595961/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-258356605528827/1125899906842624), (887681780232905/4503599627370496)), (1909319/562949953421312), by norm_num⟩
  | 1 => ⟨((5465062033/17179869184), (-4694321619/17179869184)), (41/8589934592), by norm_num⟩
  | 2 => ⟨((-15152369359/68719476736), (3253855795/17179869184)), (115/34359738368), by norm_num⟩
  | 3 => ⟨((875235175/8589934592), (-12028805175/137438953472)), (215/137438953472), by norm_num⟩
  | 4 => ⟨((-4853334351/137438953472), (8337732393/274877906944)), (151/274877906944), by norm_num⟩
  | 5 => ⟨((5382520035/549755813888), (-9246841121/1099511627776)), (169/1099511627776), by norm_num⟩
  | 6 => ⟨((-2487252391/1099511627776), (8545895803/4398046511104)), (79/2199023255552), by norm_num⟩
  | 7 => ⟨((15762578123/35184372088832), (-3384893475/8796093022208)), (63/8796093022208), by norm_num⟩
  | 8 => ⟨((-10925786585/140737488355328), (9384917475/140737488355328)), (177/140737488355328), by norm_num⟩
  | 9 => ⟨((3365856963/281474976710656), (-5782336967/562949953421312)), (55/281474976710656), by norm_num⟩
  | 10 => ⟨((-7465709645/4503599627370496), (12825633811/9007199254740992)), (123/4503599627370496), by norm_num⟩
  | 11 => ⟨((15054067175/72057594037927936), (-3232746151/18014398509481984)), (125/36028797018963968), by norm_num⟩
  | 12 => ⟨((-13912912291/576460752303423488), (46682685/2251799813685248)), (233/576460752303423488), by norm_num⟩
  | 13 => ⟨((11869164219/4611686018427387904), (-5097625047/2305843009213693952)), (25/576460752303423488), by norm_num⟩
  | 14 => ⟨((-4701187265/18446744073709551616), (2019088245/9223372036854775808)), (161/36893488147419103232), by norm_num⟩
  | 15 => ⟨((1737927839/73786976294838206464), (-11942616101/590295810358705651712)), (15/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-9637118253/4722366482869645213696), (8277990679/4722366482869645213696)), (21/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (395979991421/1267650600228229401496703205376)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890058747893325/316912650057057350374175801344), (1877206014601/316912650057057350374175801344)), (5787/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891258554320545/39614081257132168796771975168), (4223246254709/39614081257132168796771975168)), (6511/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472781916611941/618970019642690137449562112), (4486649533053/2475880078570760549798248448)), (865/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443198266646633/38685626227668133590597632), (1121507780277/38685626227668133590597632)), (3461/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551054753688375/9671406556917033397649408), (4204997069371/9671406556917033397649408)), (6491/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260101444016581/604462909807314587353088), (3678715279541/604462909807314587353088)), (2841/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889923590240207/75557863725914323419136), (1494170014127/18889465931478580854784)), (2309/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649568316729821/2361183241434822606848), (2240715849513/2361183241434822606848)), (6931/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811820917510105/295147905179352825856), (3080108041207/295147905179352825856)), (9535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456553291690195/18446744073709551616), (3848820502901/36893488147419103232)), (11927/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912866398663623/4611686018427387904), (8656230569723/9223372036854775808)), (13429/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596975099211849/1152921504606846976), (8651710291191/1152921504606846976)), (13443/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299297343504801/36028797018963968), (7565160060879/144115188075855872)), (11779/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495536391890933/36028797018963968), (5668782196875/18014398509481984)), (4425/9007199254740992), by norm_num⟩
  | 3 => ⟨((747053544785095/4503599627370496), (3538535436337/2251799813685248)), (5545/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118787039809373/2251799813685248), (882963042957/140737488355328)), (2783/281474976710656), by norm_num⟩
  | 1 => ⟨((557590317917389/562949953421312), (10562118683945/562949953421312)), (8401/281474976710656), by norm_num⟩
  | 0 => ⟨((138032858910393/140737488355328), (41980718082567/1125899906842624)), (68047/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((138032858910393/140737488355328), (41980718082567/1125899906842624)), (259578709128951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((67592271124837/70368744177664), (41173951615633/562949953421312)), (69277/562949953421312), by norm_num⟩
  | 2 => ⟨((258195663179009/281474976710656), (79098779817877/562949953421312)), (286443/1125899906842624), by norm_num⟩
  | 3 => ⟨((925138667785731/1125899906842624), (290227744581659/1125899906842624)), (606001/1125899906842624), by norm_num⟩
  | 4 => ⟨((171340588585567/281474976710656), (476953426046005/1125899906842624)), (163539/140737488355328), by norm_num⟩
  | 5 => ⟨((430299327072267/2251799813685248), (290333022500367/562949953421312)), (337657/140737488355328), by norm_num⟩
  | 6 => ⟨((-258356605528827/1125899906842624), (887681780232905/4503599627370496)), (1909319/562949953421312), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-11153595961/268435456)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-745252095/536870912), (-6474461955/134217728)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-123768632442147/1125899906842624), (252225182237431/1125899906842624)), (12334877/4503599627370496), by norm_num⟩
  | 1 => ⟨((6079038373/34359738368), (-6194164593/17179869184)), (153/34359738368), by norm_num⟩
  | 2 => ⟨((-9783834829/68719476736), (19938246663/68719476736)), (249/68719476736), by norm_num⟩
  | 3 => ⟨((5248824901/68719476736), (-21392913391/137438953472)), (269/137438953472), by norm_num⟩
  | 4 => ⟨((-8447657791/274877906944), (8607641467/137438953472)), (109/137438953472), by norm_num⟩
  | 5 => ⟨((169949759/17179869184), (-22165543221/1099511627776)), (283/1099511627776), by norm_num⟩
  | 6 => ⟨((-5835169821/2199023255552), (11891355203/2199023255552)), (153/2199023255552), by norm_num⟩
  | 7 => ⟨((1341620505/2199023255552), (-1367028421/1099511627776)), (71/4398046511104), by norm_num⟩
  | 8 => ⟨((-8637019619/70368744177664), (17601178945/70368744177664)), (115/35184372088832), by norm_num⟩
  | 9 => ⟨((1544527425/70368744177664), (-6295112155/140737488355328)), (83/140737488355328), by norm_num⟩
  | 10 => ⟨((-7954627183/2251799813685248), (2026318433/281474976710656)), (27/281474976710656), by norm_num⟩
  | 11 => ⟨((145482711/281474976710656), (-18974450669/18014398509481984)), (255/18014398509481984), by norm_num⟩
  | 12 => ⟨((-1248775417/18014398509481984), (20358800183/144115188075855872)), (69/36028797018963968), by norm_num⟩
  | 13 => ⟨((9894530463/1152921504606846976), (-20163830687/1152921504606846976)), (69/288230376151711744), by norm_num⟩
  | 14 => ⟨((-9099789973/9223372036854775808), (18544247753/9223372036854775808)), (1/36028797018963968), by norm_num⟩
  | 15 => ⟨((1952739597/18446744073709551616), (-994860513/4611686018427387904)), (111/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-6285626281/590295810358705651712), (12809329817/590295810358705651712)), (45/147573952589676412928), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (82511567509/316912650057057350374175801344)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444955679035891/158456325028528675187087900672), (3128280963855/633825300114114700748351602688)), (5783/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890927104011381/39614081257132168796771975168), (879718220573/9903520314283042199192993792)), (6507/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890775717107193/2475880078570760549798248448), (233641980693/154742504910672534362390528)), (6915/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772441360901417/154742504910672534362390528), (3737674606311/154742504910672534362390528)), (1729/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550725288433601/9671406556917033397649408), (3503435580687/9671406556917033397649408)), (3243/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((9842292349043/4722366482869645213696), (1532435907571/302231454903657293676544)), (5677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889456037346379/75557863725914323419136), (1244806862167/18889465931478580854784)), (2307/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298786393051691/4722366482869645213696), (3733380087285/4722366482869645213696)), (6923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623160943621705/590295810358705651712), (2565853493911/295147905179352825856)), (2381/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825613085794031/73786976294838206464), (6412098100279/73786976294838206464)), (1489/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456264781562473/2305843009213693952), (7210124376209/9223372036854775808)), (6705/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798151601009479/576460752303423488), (7205767660799/1152921504606846976)), (6711/576460752303423488), by norm_num⟩
  | 5 => ⟨((598301729021307/72057594037927936), (3150073228373/72057594037927936)), (5879/72057594037927936), by norm_num⟩
  | 4 => ⟨((747330751087127/18014398509481984), (9440421845951/36028797018963968)), (17663/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493020441103585/9007199254740992), (11783387081157/9007199254740992)), (5531/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117710819323461/2251799813685248), (2939422194881/562949953421312)), (11097/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113592313548987/1125899906842624), (8786164893285/562949953421312)), (33465/1125899906842624), by norm_num⟩
  | 0 => ⟨((34412184076193/35184372088832), (34888102177179/1125899906842624)), (67629/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((34412184076193/35184372088832), (34888102177179/1125899906842624)), (257984165671920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1075941109655891/1125899906842624), (533162755807/8796093022208)), (68241/562949953421312), by norm_num⟩
  | 2 => ⟨((512031268163411/562949953421312), (130433301617399/1125899906842624)), (138699/562949953421312), by norm_num⟩
  | 3 => ⟨((916325888178189/1125899906842624), (237271282933795/1125899906842624)), (71111/140737488355328), by norm_num⟩
  | 4 => ⟨((1391518849730207/2251799813685248), (386211629918677/1125899906842624)), (582883/562949953421312), by norm_num⟩
  | 5 => ⟨((297470274372261/1125899906842624), (954651048020711/2251799813685248)), (560141/281474976710656), by norm_num⟩
  | 6 => ⟨((-123768632442147/1125899906842624), (252225182237431/1125899906842624)), (12334877/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-6474461955/134217728)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-28831627307/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-459263771968319/2251799813685248), (280128836035721/4503599627370496)), (5186485/2251799813685248), by norm_num⟩
  | 1 => ⟨((12556308171/34359738368), (-7658744729/68719476736)), (143/34359738368), by norm_num⟩
  | 2 => ⟨((-703058877/2147483648), (6861314195/68719476736)), (129/34359738368), by norm_num⟩
  | 3 => ⟨((6718466135/34359738368), (-512242695/8589934592)), (155/68719476736), by norm_num⟩
  | 4 => ⟨((-24075750633/274877906944), (7342525595/274877906944)), (35/34359738368), by norm_num⟩
  | 5 => ⟨((8627590835/274877906944), (-5262415905/549755813888)), (203/549755813888), by norm_num⟩
  | 6 => ⟨((-10305711717/1099511627776), (6285989019/2199023255552)), (61/549755813888), by norm_num⟩
  | 7 => ⟨((5275816159/2199023255552), (-6435988771/8796093022208)), (63/2199023255552), by norm_num⟩
  | 8 => ⟨((-9452993561/17592186044416), (720733989/4398046511104)), (227/35184372088832), by norm_num⟩
  | 9 => ⟨((940971707/8796093022208), (-4591580265/140737488355328)), (91/70368744177664), by norm_num⟩
  | 10 => ⟨((-21580735569/1125899906842624), (6581605935/1125899906842624)), (131/562949953421312), by norm_num⟩
  | 11 => ⟨((3515226119/1125899906842624), (-4288238093/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 12 => ⟨((-16795839161/36028797018963968), (5122327473/36028797018963968)), (207/36028797018963968), by norm_num⟩
  | 13 => ⟨((9259724265/144115188075855872), (-2823993463/144115188075855872)), (115/144115188075855872), by norm_num⟩
  | 14 => ⟨((-4740342467/576460752303423488), (2891381159/1152921504606846976)), (237/2305843009213693952), by norm_num⟩
  | 15 => ⟨((9059790403/9223372036854775808), (-1381509219/4611686018427387904)), (57/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-4058241311/36893488147419103232), (2475332225/73786976294838206464)), (103/73786976294838206464), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (231667610919/633825300114114700748351602688)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444893745767779/158456325028528675187087900672), (4390496563761/633825300114114700748351602688)), (5791/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472662036995163/9903520314283042199192993792), (2469303042405/19807040628566084398385987584)), (1629/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472619749073131/618970019642690137449562112), (5246438312235/2475880078570760549798248448)), (6925/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221518033626151/19342813113834066795298816), (5245503687445/154742504910672534362390528)), (6927/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387611592684553/2417851639229258349412352), (4916666640683/9671406556917033397649408)), (6497/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259568973898697/604462909807314587353088), (4301090213269/604462909807314587353088)), (711/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944529036749039/37778931862957161709568), (6987409473545/75557863725914323419136)), (4623/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649243637547625/2361183241434822606848), (1309731920617/1180591620717411303424)), (6939/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811374304596249/295147905179352825856), (3600438815275/295147905179352825856)), (4773/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825096098648493/73786976294838206464), (8997124929229/73786976294838206464)), (5971/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912237680514339/4611686018427387904), (1264537944821/1152921504606846976)), (1681/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797858373853521/576460752303423488), (5054737788061/576460752303423488)), (1683/144115188075855872), by norm_num⟩
  | 5 => ⟨((598043645575713/72057594037927936), (4419054486743/72057594037927936)), (1475/18014398509481984), by norm_num⟩
  | 4 => ⟨((746940613870899/18014398509481984), (3310449373127/9007199254740992)), (17737/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492034588820629/9007199254740992), (8262676391379/4503599627370496)), (22237/9007199254740992), by norm_num⟩
  | 2 => ⟨((139588658623077/281474976710656), (8242502299323/1125899906842624)), (22335/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112050973035733/1125899906842624), (24626612711629/1125899906842624)), (33747/1125899906842624), by norm_num⟩
  | 0 => ⟨((68622033040569/70368744177664), (24424757083847/562949953421312)), (535/8796093022208), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((68622033040569/70368744177664), (24424757083847/562949953421312)), (2040863070663807/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((1068579429504039/1125899906842624), (95273917828287/1125899906842624)), (8719/70368744177664), by norm_num⟩
  | 2 => ⟨((1006115082572047/1125899906842624), (180846890812997/1125899906842624)), (144207/562949953421312), by norm_num⟩
  | 3 => ⟨((870025794929877/1125899906842624), (323213073164681/1125899906842624)), (608113/1125899906842624), by norm_num⟩
  | 4 => ⟨((289758525253173/562949953421312), (31219883446435/70368744177664)), (161121/140737488355328), by norm_num⟩
  | 5 => ⟨((76669021789821/1125899906842624), (1028436984826721/2251799813685248)), (308829/140737488355328), by norm_num⟩
  | 6 => ⟨((-459263771968319/2251799813685248), (280128836035721/4503599627370496)), (5186485/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-28831627307/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-901055955/536870912), (-3914012815/67108864)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-85109330278381/2251799813685248), (-823330204162201/4503599627370496)), (17716747/9007199254740992), by norm_num⟩
  | 1 => ⟨((5054172045/68719476736), (12223255923/34359738368)), (265/68719476736), by norm_num⟩
  | 2 => ⟨((-4917482339/68719476736), (-23785357755/68719476736)), (65/17179869184), by norm_num⟩
  | 3 => ⟨((3189659597/68719476736), (482126761/2147483648)), (85/34359738368), by norm_num⟩
  | 4 => ⟨((-3103395491/137438953472), (-7505402859/68719476736)), (167/137438953472), by norm_num⟩
  | 5 => ⟨((2415571513/274877906944), (11683871677/274877906944)), (261/549755813888), by norm_num⟩
  | 6 => ⟨((-3133656749/1099511627776), (-7578588159/549755813888)), (171/1099511627776), by norm_num⟩
  | 7 => ⟨((871116353/1099511627776), (16854001845/4398046511104)), (3/68719476736), by norm_num⟩
  | 8 => ⟨((-3390228305/17592186044416), (-16398186621/17592186044416)), (189/17592186044416), by norm_num⟩
  | 9 => ⟨((5864070815/140737488355328), (28363909131/140737488355328)), (329/140737488355328), by norm_num⟩
  | 10 => ⟨((-2282190983/281474976710656), (-11038723729/281474976710656)), (129/281474976710656), by norm_num⟩
  | 11 => ⟨((807443381/562949953421312), (3905520825/562949953421312)), (23/281474976710656), by norm_num⟩
  | 12 => ⟨((-2094949693/9007199254740992), (-20266113629/18014398509481984)), (15/1125899906842624), by norm_num⟩
  | 13 => ⟨((5017333993/144115188075855872), (24268329965/144115188075855872)), (289/144115188075855872), by norm_num⟩
  | 14 => ⟨((-5579017793/1152921504606846976), (-26985136903/1152921504606846976)), (323/1152921504606846976), by norm_num⟩
  | 15 => ⟨((5790009251/9223372036854775808), (14002840473/4611686018427387904)), (337/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-2816709441/36893488147419103232), (-1703016837/4611686018427387904)), (165/36893488147419103232), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-2311703351419/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889688080413339/316912650057057350374175801344), (-684392478571/158456325028528675187087900672)), (1445/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890424872188659/39614081257132168796771975168), (-1539652113489/19807040628566084398385987584)), (813/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472560567463059/618970019642690137449562112), (-3271199790835/2475880078570760549798248448)), (6911/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885954054718929/77371252455336267181195264), (-3270568808429/154742504910672534362390528)), (6913/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550225573176479/9671406556917033397649408), (-766371986925/2417851639229258349412352)), (3241/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259376377774347/604462909807314587353088), (-670407941535/151115727451828646838272)), (5673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59023319763667/2361183241434822606848), (-4356395276787/75557863725914323419136)), (4611/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324563595090173/1180591620717411303424), (-3266197416807/4722366482869645213696)), (6919/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811214990054747/295147905179352825856), (-4489235993453/590295810358705651712)), (4759/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456175053002323/18446744073709551616), (-2804433830743/36893488147419103232)), (11903/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456008321208667/2305843009213693952), (-6306296174041/9223372036854775808)), (6699/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398819696714741/288230376151711744), (-787712289873/144115188075855872)), (13409/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298927174575631/36028797018963968), (-5508816297551/144115188075855872)), (367/4503599627370496), by norm_num⟩
  | 4 => ⟨((1493322567080729/36028797018963968), (-4126446061409/18014398509481984)), (2205/4503599627370496), by norm_num⟩
  | 3 => ⟨((745676187216929/4503599627370496), (-1287256206835/1125899906842624)), (11045/4503599627370496), by norm_num⟩
  | 2 => ⟨((558025572258913/1125899906842624), (-5135491774425/1125899906842624)), (22151/2251799813685248), by norm_num⟩
  | 1 => ⟨((138890467613723/140737488355328), (-15338922592035/1125899906842624)), (16689/562949953421312), by norm_num⟩
  | 0 => ⟨((1096336262254445/1125899906842624), (-7602077433231/281474976710656)), (33685/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096336262254445/1125899906842624), (-7602077433231/281474976710656)), (128498079540061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1066727625905303/1125899906842624), (-29609854687313/562949953421312)), (67421/562949953421312), by norm_num⟩
  | 2 => ⟨((2015100715431027/2251799813685248), (-112214770787483/1125899906842624)), (2107/8796093022208), by norm_num⟩
  | 3 => ⟨((445228551160147/562949953421312), (-401677029230615/2251799813685248)), (1072907/2251799813685248), by norm_num⟩
  | 4 => ⟨((668423309697427/1125899906842624), (-635360499354429/2251799813685248)), (259983/281474976710656), by norm_num⟩
  | 5 => ⟨((614386728002865/2251799813685248), (-23575017928351/70368744177664)), (455405/281474976710656), by norm_num⟩
  | 6 => ⟨((-85109330278381/2251799813685248), (-823330204162201/4503599627370496)), (17716747/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-3914012815/67108864)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-481443911/268435456), (-16730393941/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((655287391831521/4503599627370496), (726691946789709/9007199254740992)), (8834441/4503599627370496), by norm_num⟩
  | 1 => ⟨((-20792111577/68719476736), (-11528880479/68719476736)), (283/68719476736), by norm_num⟩
  | 2 => ⟨((5404497569/17179869184), (11986816499/68719476736)), (297/68719476736), by norm_num⟩
  | 3 => ⟨((-14984449009/68719476736), (-2077157015/17179869184)), (13/4294967296), by norm_num⟩
  | 4 => ⟨((7789821437/68719476736), (8638653171/137438953472)), (219/137438953472), by norm_num⟩
  | 5 => ⟨((-12958782639/274877906944), (-7185429707/274877906944)), (23/34359738368), by norm_num⟩
  | 6 => ⟨((4491171825/274877906944), (9961120685/1099511627776)), (129/549755813888), by norm_num⟩
  | 7 => ⟨((-10673290587/2199023255552), (-2959081165/1099511627776)), (155/2199023255552), by norm_num⟩
  | 8 => ⟨((11097241917/8796093022208), (1538309075/2199023255552)), (163/8796093022208), by norm_num⟩
  | 9 => ⟨((-20512058525/70368744177664), (-5686797857/35184372088832)), (19/4398046511104), by norm_num⟩
  | 10 => ⟨((17061450641/281474976710656), (4730145481/140737488355328)), (255/281474976710656), by norm_num⟩
  | 11 => ⟨((-6450598041/562949953421312), (-7153498917/1125899906842624)), (195/1125899906842624), by norm_num⟩
  | 12 => ⟨((4471213845/2251799813685248), (9916855211/9007199254740992)), (273/9007199254740992), by norm_num⟩
  | 13 => ⟨((-11443234229/36028797018963968), (-6345083289/36028797018963968)), (11/2251799813685248), by norm_num⟩
  | 14 => ⟨((13597449501/288230376151711744), (117805623/4503599627370496)), (211/288230376151711744), by norm_num⟩
  | 15 => ⟨((-15080054055/2305843009213693952), (-8361639469/2305843009213693952)), (59/576460752303423488), by norm_num⟩
  | 16 => ⟨((7839522713/9223372036854775808), (4346885117/9223372036854775808)), (31/2305843009213693952), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395409877308005/2535301200456458802993406410752), (41217794221/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55600068675829/19807040628566084398385987584), (780827938027/633825300114114700748351602688)), (11535/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890229406117681/39614081257132168796771975168), (439146476925/19807040628566084398385987584)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890034895689817/2475880078570760549798248448), (933015532325/2475880078570760549798248448)), (6895/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771701082183541/154742504910672534362390528), (932823518203/154742504910672534362390528)), (13791/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550031853537763/9671406556917033397649408), (218579521949/2417851639229258349412352)), (6465/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259207241302827/604462909807314587353088), (764824427603/604462909807314587353088)), (5657/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944236037822391/37778931862957161709568), (1242457514039/75557863725914323419136)), (18387/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162256170758613/590295810358705651712), (232877214371/1180591620717411303424)), (431/147573952589676412928), by norm_num⟩
  | 9 => ⟨((811074532514941/295147905179352825856), (160035215147/73786976294838206464)), (9483/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456087634031605/18446744073709551616), (199942267673/9223372036854775808)), (11855/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455910478915533/2305843009213693952), (1798361838193/9223372036854775808)), (26679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594889934546081/1152921504606846976), (898482331707/576460752303423488)), (6671/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195371279345895/144115188075855872), (98173355379/9007199254740992)), (5839/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492822080668249/36028797018963968), (588255826207/9007199254740992)), (17523/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490736613866929/9007199254740992), (1467898499715/4503599627370496)), (43831/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230900206064947/4503599627370496), (5855179600389/4503599627370496)), (21933/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110258794469613/1125899906842624), (8741845179881/2251799813685248)), (131773/2251799813685248), by norm_num⟩
  | 0 => ⟨((68421984016025/70368744177664), (2165082804885/281474976710656)), (4129/35184372088832), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((68421984016025/70368744177664), (2165082804885/281474976710656)), (15750885143983353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2128797369876875/2251799813685248), (33682968266751/2251799813685248)), (517957/2251799813685248), by norm_num⟩
  | 2 => ⟨((503002495171705/562949953421312), (31843067851825/1125899906842624)), (994825/2251799813685248), by norm_num⟩
  | 3 => ⟨((1795953713968907/2251799813685248), (56904321551307/1125899906842624)), (1834049/2251799813685248), by norm_num⟩
  | 4 => ⟨((1426635403356015/2251799813685248), (181539277177035/2251799813685248)), (3110933/2251799813685248), by norm_num⟩
  | 5 => ⟨((1778428129162907/4503599627370496), (57507412147921/562949953421312)), (8886979/4503599627370496), by norm_num⟩
  | 6 => ⟨((655287391831521/4503599627370496), (726691946789709/9007199254740992)), (8834441/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-481443911/268435456), (-16730393941/268435456)), (1/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile052Terms0

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
namespace Reinmann.XiBand97.Tile032Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63841/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63841/2560))
  have he : value ((69/80), (63841/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-1160018897/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((102986985127825/1125899906842624), (-11321493416731/4503599627370496)), (209666611/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1089250769/4294967296), (29935689/4294967296)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((1510022199/4294967296), (-41499677/4294967296)), (49/1073741824), by norm_num⟩
  | 3 => ⟨((-174444605/536870912), (38353845/4294967296)), (183/4294967296), by norm_num⟩
  | 4 => ⟨((967326289/4294967296), (-53169719/8589934592)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-67049949/536870912), (29483553/8589934592)), (9/536870912), by norm_num⟩
  | 6 => ⟨((991476973/17179869184), (-27248589/17179869184)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((-1570833071/68719476736), (10792733/17179869184)), (107/34359738368), by norm_num⟩
  | 8 => ⟨((544409257/68719476736), (-14961905/68719476736)), (75/68719476736), by norm_num⟩
  | 9 => ⟨((-1341709303/549755813888), (9218491/137438953472)), (187/549755813888), by norm_num⟩
  | 10 => ⟨((1488003233/2199023255552), (-40894535/2199023255552)), (209/2199023255552), by norm_num⟩
  | 11 => ⟨((-375056453/2199023255552), (20615223/4398046511104)), (53/2199023255552), by norm_num⟩
  | 12 => ⟨((86656441/2199023255552), (-38105023/35184372088832)), (99/17592186044416), by norm_num⟩
  | 13 => ⟨((-1182831611/140737488355328), (8126889/35184372088832)), (171/140737488355328), by norm_num⟩
  | 14 => ⟨((234250399/140737488355328), (-51502905/1125899906842624)), (137/562949953421312), by norm_num⟩
  | 15 => ⟨((-346389341/1125899906842624), (38079033/4503599627370496)), (51/1125899906842624), by norm_num⟩
  | 16 => ⟨((1920790361/36028797018963968), (-52788749/36028797018963968)), (285/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-2236902485/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889140468287801/316912650057057350374175801344), (-42333983647/633825300114114700748351602688)), (23051/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889193195138673/39614081257132168796771975168), (-47615869423/39614081257132168796771975168)), (207461/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((7378649142397/9671406556917033397649408), (-6322440745/309485009821345068724781056)), (55107/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770600658121397/154742504910672534362390528), (-50565655035/154742504910672534362390528)), (55107/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549000515245819/9671406556917033397649408), (-47390569123/9671406556917033397649408)), (51663/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629152564722145/302231454903657293676544), (-41452021571/604462909807314587353088)), (90411/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471751680817877/18889465931478580854784), (-2104122997/2361183241434822606848)), (293837/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162118857313463/590295810358705651712), (-25237407769/2361183241434822606848)), (55095/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810319720038097/295147905179352825856), (-69363673841/590295810358705651712)), (18939/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822464738518017/73786976294838206464), (-86645838175/73786976294838206464)), (378783/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227690261022669/1152921504606846976), (-97395849477/9223372036854775808)), (53267/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398193055894883/288230376151711744), (-24323763493/288230376151711744)), (426143/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193520660551853/144115188075855872), (-42509959087/72057594037927936)), (372883/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490050902147167/36028797018963968), (-127303720911/36028797018963968)), (139835/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487280937061687/9007199254740992), (-19841833457/1125899906842624)), (174801/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112006839653061/2251799813685248), (-79071884709/1125899906842624)), (349625/1125899906842624), by norm_num⟩
  | 1 => ⟨((2210249648810113/2251799813685248), (-471487826575/2251799813685248)), (2097997/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169213709827711/2251799813685248), (-931267548915/2251799813685248)), (2098541/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169213709827711/2251799813685248), (-931267548915/2251799813685248)), (8005298618796920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2089656115542683/2251799813685248), (-897112755027/1125899906842624)), (505611/140737488355328), by norm_num⟩
  | 2 => ⟨((242398293769361/281474976710656), (-1665030029295/1125899906842624)), (1878427/281474976710656), by norm_num⟩
  | 3 => ⟨((834983773529317/1125899906842624), (-5735507189909/2251799813685248)), (25926819/2251799813685248), by norm_num⟩
  | 4 => ⟨((1238457652957295/2251799813685248), (-8507071378955/2251799813685248)), (19293745/1125899906842624), by norm_num⟩
  | 5 => ⟨((1362203672443703/4503599627370496), (-18715069766843/4503599627370496)), (85473389/4503599627370496), by norm_num⟩
  | 6 => ⟨((102986985127825/1125899906842624), (-11321493416731/4503599627370496)), (209666611/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1160018897/16777216)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-40997585/16777216), (-592691767/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((49225023676229/18014398509481984), (-781830287583235/9007199254740992)), (501428385/18014398509481984), by norm_num⟩
  | 1 => ⟨((-16625523/2147483648), (33007443/134217728)), (85/1073741824), by norm_num⟩
  | 2 => ⟨((23551827/2147483648), (-1496274047/4294967296)), (121/1073741824), by norm_num⟩
  | 3 => ⟨((-11121225/1073741824), (706543933/2147483648)), (459/4294967296), by norm_num⟩
  | 4 => ⟨((31508803/4294967296), (-2001789699/8589934592)), (163/2147483648), by norm_num⟩
  | 5 => ⟨((-2231779/536870912), (567149729/4294967296)), (93/2147483648), by norm_num⟩
  | 6 => ⟨((1053851/536870912), (-535618727/8589934592)), (353/17179869184), by norm_num⟩
  | 7 => ⟨((-27298603/34359738368), (216788875/8589934592)), (287/34359738368), by norm_num⟩
  | 8 => ⟨((38671383/137438953472), (-1228418267/137438953472)), (51/17179869184), by norm_num⟩
  | 9 => ⟨((-48695235/549755813888), (1546831567/549755813888)), (129/137438953472), by norm_num⟩
  | 10 => ⟨((13796399/549755813888), (-1753001535/2199023255552)), (587/2199023255552), by norm_num⟩
  | 11 => ⟨((-56855479/8796093022208), (903023153/4398046511104)), (607/8796093022208), by norm_num⟩
  | 12 => ⟨((53694567/35184372088832), (-1705638165/35184372088832)), (575/35184372088832), by norm_num⟩
  | 13 => ⟨((-23404333/70368744177664), (743451817/70368744177664)), (503/140737488355328), by norm_num⟩
  | 14 => ⟨((37891125/562949953421312), (-1203632919/562949953421312)), (409/562949953421312), by norm_num⟩
  | 15 => ⟨((-57255275/4503599627370496), (454686513/1125899906842624)), (155/1125899906842624), by norm_num⟩
  | 16 => ⟨((20277051/9007199254740992), (-161027987/2251799813685248)), (441/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-2005144095869/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778197362047067/633825300114114700748351602688), (-148221160517/39614081257132168796771975168)), (184867/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889099025998523/39614081257132168796771975168), (-2667412486879/39614081257132168796771975168)), (208005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888833928431769/2475880078570760549798248448), (-708354785105/618970019642690137449562112)), (221041/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221312523046501/19342813113834066795298816), (-2832624479115/154742504910672534362390528)), (27635/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548906085707411/9671406556917033397649408), (-1327370697851/4835703278458516698824704)), (25913/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314555567102633/151115727451828646838272), (-1161027488095/302231454903657293676544)), (181433/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943435816781117/37778931862957161709568), (-3771757969503/75557863725914323419136)), (294905/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648424578104789/2361183241434822606848), (-2827435436077/4722366482869645213696)), (3457/73786976294838206464), by norm_num⟩
  | 9 => ⟨((810249487301245/295147905179352825856), (-971369377575/147573952589676412928)), (304327/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455572055229829/18446744073709551616), (-4853479713283/73786976294838206464)), (380575/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455330555398461/2305843009213693952), (-1363884574749/2305843009213693952)), (53547/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796285377595157/576460752303423488), (-1362440138073/288230376151711744)), (428663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596671289285303/72057594037927936), (-4762047698655/144115188075855872)), (93851/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489780197085361/36028797018963968), (-7130103912501/36028797018963968)), (563753/36028797018963968), by norm_num⟩
  | 3 => ⟨((743468157220679/4503599627370496), (-2222494207907/2251799813685248)), (705825/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111652909656111/2251799813685248), (-17712155459921/4503599627370496)), (1415061/4503599627370496), by norm_num⟩
  | 1 => ⟨((552285425597477/562949953421312), (-26399300016047/2251799813685248)), (266393/281474976710656), by norm_num⟩
  | 0 => ⟨((2166815462131545/2251799813685248), (-26063116383271/1125899906842624)), (2148325/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166815462131545/2251799813685248), (-26063116383271/1125899906842624)), (8195209507468795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((130239488715653/140737488355328), (-50158955718343/1125899906842624)), (2116977/562949953421312), by norm_num⟩
  | 2 => ⟨((1923923850632623/2251799813685248), (-92834920156805/1125899906842624)), (4106755/562949953421312), by norm_num⟩
  | 3 => ⟨((1628479437268283/2251799813685248), (-317270329228685/2251799813685248)), (7694809/562949953421312), by norm_num⟩
  | 4 => ⟨((1132998057949639/2251799813685248), (-458893551783969/2251799813685248)), (53191845/2251799813685248), by norm_num⟩
  | 5 => ⟨((953105423427967/4503599627370496), (-923573223191541/4503599627370496)), (150414177/4503599627370496), by norm_num⟩
  | 6 => ⟨((49225023676229/18014398509481984), (-781830287583235/9007199254740992)), (501428385/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-592691767/8388608)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2614043/1048576), (-1209297951/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-732975667329629/9007199254740992), (-261999970526153/18014398509481984)), (508702567/18014398509481984), by norm_num⟩
  | 1 => ⟨((252553483/1073741824), (90274491/2147483648)), (353/4294967296), by norm_num⟩
  | 2 => ⟨((-729973455/2147483648), (-260926839/4294967296)), (513/4294967296), by norm_num⟩
  | 3 => ⟨((1406596439/4294967296), (251391855/4294967296)), (497/4294967296), by norm_num⟩
  | 4 => ⟨((-63524791/268435456), (-45413495/1073741824)), (361/4294967296), by norm_num⟩
  | 5 => ⟨((293776419/2147483648), (210019013/8589934592)), (419/8589934592), by norm_num⟩
  | 6 => ⟨((-566082043/8589934592), (-202344341/17179869184)), (203/8589934592), by norm_num⟩
  | 7 => ⟨((467482157/17179869184), (167100105/34359738368)), (337/34359738368), by norm_num⟩
  | 8 => ⟨((-168899653/17179869184), (-30186339/17179869184)), (489/137438953472), by norm_num⟩
  | 9 => ⟨((1735761021/549755813888), (38777663/68719476736)), (315/274877906944), by norm_num⟩
  | 10 => ⟨((-1003398927/1099511627776), (-179330979/1099511627776)), (183/549755813888), by norm_num⟩
  | 11 => ⟨((1054616699/4398046511104), (188484799/4398046511104)), (193/2199023255552), by norm_num⟩
  | 12 => ⟨((-254019527/4398046511104), (-181597047/17592186044416)), (187/8796093022208), by norm_num⟩
  | 13 => ⟨((56477759/4398046511104), (80751227/35184372088832)), (167/35184372088832), by norm_num⟩
  | 14 => ⟨((-746247861/281474976710656), (-266744075/562949953421312)), (277/281474976710656), by norm_num⟩
  | 15 => ⟨((1150364663/2251799813685248), (205597211/2251799813685248)), (429/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1662490767/18014398509481984), (-148563093/9007199254740992)), (311/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-3861900198969/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889056623095663/316912650057057350374175801344), (-2283601380459/316912650057057350374175801344)), (185299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889003963539891/39614081257132168796771975168), (-5136964167907/39614081257132168796771975168)), (26065/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((7377860736613/9671406556917033397649408), (-2728316734299/1237940039285380274899124224)), (221619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770397957169195/154742504910672534362390528), (-5455068834825/154742504910672534362390528)), (221695/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548809560443939/9671406556917033397649408), (-2556232474469/4835703278458516698824704)), (207919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258137122153887/604462909807314587353088), (-4471745127941/604462909807314587353088)), (182009/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886731984719327/75557863725914323419136), (-7263470951587/75557863725914323419136)), (295915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324185823866923/1180591620717411303424), (-680609812941/590295810358705651712)), (55517/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810175795914499/295147905179352825856), (-3741140904843/295147905179352825856)), (152779/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822101260312499/73786976294838206464), (-9346215726937/73786976294838206464)), (95567/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821108141102629/9223372036854775808), (-10505371788421/9223372036854775808)), (430493/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592351997753145/1152921504606846976), (-10493977159955/1152921504606846976)), (431045/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149143239801699/18014398509481984), (-9169420005977/144115188075855872)), (377787/144115188075855872), by norm_num⟩
  | 4 => ⟨((186184343426065/4503599627370496), (-6864266192155/18014398509481984)), (567927/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486536277728983/9007199254740992), (-8557960042845/4503599627370496)), (178023/2251799813685248), by norm_num⟩
  | 2 => ⟨((277806423614879/562949953421312), (-8524451524137/1125899906842624)), (715375/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103862635058629/1125899906842624), (-25406166374347/1125899906842624)), (1081291/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081725029276537/1125899906842624), (-50145711908313/1125899906842624)), (2195637/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1081725029276537/1125899906842624), (-50145711908313/1125899906842624)), (8375690464500045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037049953947407/1125899906842624), (-48178236229035/562949953421312)), (4414563/1125899906842624), by norm_num⟩
  | 2 => ⟨((1893930411962963/2251799813685248), (-177505077881037/1125899906842624)), (17775983/2251799813685248), by norm_num⟩
  | 3 => ⟨((384241549096663/562949953421312), (-597179666209425/2251799813685248)), (35506825/2251799813685248), by norm_num⟩
  | 4 => ⟨((445341882282791/1125899906842624), (-203802521555241/562949953421312)), (33651635/1125899906842624), by norm_num⟩
  | 5 => ⟨((114353045951821/4503599627370496), (-1289802733074767/4503599627370496)), (203947503/4503599627370496), by norm_num⟩
  | 6 => ⟨((-732975667329629/9007199254740992), (-261999970526153/18014398509481984)), (508702567/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1209297951/16777216)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-1231919047/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-138153695057019/4503599627370496), (1309501662393711/18014398509481984)), (252087063/9007199254740992), by norm_num⟩
  | 1 => ⟨((193970263/2147483648), (-919281897/4294967296)), (355/4294967296), by norm_num⟩
  | 2 => ⟨((-571133603/4294967296), (1353384725/4294967296)), (525/4294967296), by norm_num⟩
  | 3 => ⟨((280278007/2147483648), (-1328319579/4294967296)), (259/2147483648), by norm_num⟩
  | 4 => ⟨((-51578843/536870912), (488894493/2147483648)), (383/4294967296), by norm_num⟩
  | 5 => ⟨((485986419/8589934592), (-1151616001/8589934592)), (453/8589934592), by norm_num⟩
  | 6 => ⟨((-476985785/17179869184), (1130287681/17179869184)), (447/17179869184), by norm_num⟩
  | 7 => ⟨((401273011/34359738368), (-950875173/34359738368)), (189/17179869184), by norm_num⟩
  | 8 => ⟨((-590761947/137438953472), (699948481/68719476736)), (559/137438953472), by norm_num⟩
  | 9 => ⟨((386547223/274877906944), (-915980263/274877906944)), (23/17179869184), by norm_num⟩
  | 10 => ⟨((-113816471/274877906944), (269704799/274877906944)), (435/1099511627776), by norm_num⟩
  | 11 => ⟨((60931937/549755813888), (-1155097197/4398046511104)), (117/1099511627776), by norm_num⟩
  | 12 => ⟨((-239213827/8796093022208), (283426101/4398046511104)), (461/17592186044416), by norm_num⟩
  | 13 => ⟨((54180809/8796093022208), (-128389363/8796093022208)), (419/70368744177664), by norm_num⟩
  | 14 => ⟨((-11395149/8796093022208), (216019797/70368744177664)), (177/140737488355328), by norm_num⟩
  | 15 => ⟨((143156569/562949953421312), (-339230459/562949953421312)), (279/1125899906842624), by norm_num⟩
  | 16 => ⟨((-210757891/4503599627370496), (499421693/4503599627370496)), (413/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (2566309728997/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444511913550871/158456325028528675187087900672), (3034763613123/633825300114114700748351602688)), (184997/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944465267708415/19807040628566084398385987584), (1706675672319/19807040628566084398385987584)), (208161/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944327405569841/1237940039285380274899124224), (3625745728535/2475880078570760549798248448)), (6913/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770320959182761/154742504910672534362390528), (3624688498125/154742504910672534362390528)), (110633/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548737947570213/9671406556917033397649408), (849255627365/2417851639229258349412352)), (103745/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629037516575773/302231454903657293676544), (2971272131591/604462909807314587353088)), (181607/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886632162070267/75557863725914323419136), (4826213241631/75557863725914323419136)), (295211/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296669365451909/4722366482869645213696), (113056868467/147573952589676412928)), (27687/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405062864685067/147573952589676412928), (4971513550449/590295810358705651712)), (152349/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821978371662321/73786976294838206464), (1552477921029/18446744073709551616)), (381087/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820973017843119/9223372036854775808), (6979994744711/9223372036854775808)), (53627/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796110387260463/576460752303423488), (435769158767/72057594037927936)), (429383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149129434317841/18014398509481984), (3046064079537/72057594037927936)), (94031/36028797018963968), by norm_num⟩
  | 4 => ⟨((186164725858961/4503599627370496), (4560467505213/18014398509481984)), (282507/18014398509481984), by norm_num⟩
  | 3 => ⟨((371588827295755/2251799813685248), (5685510045453/4503599627370496)), (707719/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222134825342387/4503599627370496), (22651799844689/4503599627370496)), (709901/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207362993397917/2251799813685248), (33752817768095/2251799813685248)), (535161/562949953421312), by norm_num⟩
  | 0 => ⟨((540792651945507/562949953421312), (33305206164391/1125899906842624)), (4325243/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((540792651945507/562949953421312), (33305206164391/1125899906842624)), (16499492653853606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076059382779087/2251799813685248), (127977349714803/2251799813685248)), (2141475/562949953421312), by norm_num⟩
  | 2 => ⟨((1906761130670035/2251799813685248), (235978861037205/2251799813685248)), (8384209/1125899906842624), by norm_num⟩
  | 3 => ⟨((1589862457941417/2251799813685248), (399640604951593/2251799813685248)), (31912571/2251799813685248), by norm_num⟩
  | 4 => ⟨((525790527127301/1125899906842624), (564325115065797/2251799813685248)), (28195295/1125899906842624), by norm_num⟩
  | 5 => ⟨((43707253270697/281474976710656), (1054149833100909/4503599627370496)), (80932509/2251799813685248), by norm_num⟩
  | 6 => ⟨((-138153695057019/4503599627370496), (1309501662393711/18014398509481984)), (252087063/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1231919047/16777216)), (1/8388608), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-626689783/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((130988376172145/2251799813685248), (433301586160893/9007199254740992)), (294266657/18014398509481984), by norm_num⟩
  | 1 => ⟨((-374227625/2147483648), (-309480559/2147483648)), (53/1073741824), by norm_num⟩
  | 2 => ⟨((560542887/2147483648), (927120899/4294967296)), (5/67108864), by norm_num⟩
  | 3 => ⟨((-1119490945/4294967296), (-57862625/268435456)), (161/2147483648), by norm_num⟩
  | 4 => ⟨((838423789/4294967296), (693363733/4294967296)), (243/4294967296), by norm_num⟩
  | 5 => ⟨((-502338641/4294967296), (-830852845/8589934592)), (293/8589934592), by norm_num⟩
  | 6 => ⟨((1003248053/17179869184), (414835447/8589934592)), (295/17179869184), by norm_num⟩
  | 7 => ⟨((-107337949/4294967296), (-710134821/34359738368)), (127/17179869184), by norm_num⟩
  | 8 => ⟨((160777879/17179869184), (531843451/68719476736)), (3/1073741824), by norm_num⟩
  | 9 => ⟨((-856262189/274877906944), (-354057909/137438953472)), (129/137438953472), by norm_num⟩
  | 10 => ⟨((513026455/549755813888), (212132541/274877906944)), (311/1099511627776), by norm_num⟩
  | 11 => ⟨((-1117738115/4398046511104), (-231088109/1099511627776)), (341/4398046511104), by norm_num⟩
  | 12 => ⟨((69759253/1099511627776), (923037475/17592186044416)), (343/17592186044416), by norm_num⟩
  | 13 => ⟨((-128603105/8796093022208), (-850822509/70368744177664)), (159/35184372088832), by norm_num⟩
  | 14 => ⟨((880595365/281474976710656), (364119493/140737488355328)), (137/140737488355328), by norm_num⟩
  | 15 => ⟨((-703474121/1125899906842624), (-581762409/1125899906842624)), (221/1125899906842624), by norm_num⟩
  | 16 => ⟨((65856879/562949953421312), (217850553/2251799813685248)), (333/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (900078449809/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777983839194513/633825300114114700748351602688), (532150446877/316912650057057350374175801344)), (92305/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944429499481791/19807040628566084398385987584), (1197071396029/39614081257132168796771975168)), (207699/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236072392803027/309485009821345068724781056), (635776640543/1237940039285380274899124224)), (220697/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770245671183613/154742504910672534362390528), (1271176500855/154742504910672534362390528)), (110357/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548667769277659/9671406556917033397649408), (74457987179/604462909807314587353088)), (103469/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258014031009495/604462909807314587353088), (1042011819487/604462909807314587353088)), (90545/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886533790106543/75557863725914323419136), (846259786807/37778931862957161709568)), (147153/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324149061926095/1180591620717411303424), (634367059971/2361183241434822606848)), (27595/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405037998741537/147573952589676412928), (217930602533/73786976294838206464)), (75899/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821855649256081/73786976294838206464), (136106896333/4611686018427387904)), (189785/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227604645165437/1152921504606846976), (2447732029807/9223372036854775808)), (26695/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592087669944643/1152921504606846976), (19101522177/9007199254740992)), (427249/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74557631001555/9007199254740992), (1068147590161/72057594037927936)), (186995/72057594037927936), by norm_num⟩
  | 4 => ⟨((186144236903865/4503599627370496), (195208877/2199023255552)), (280639/18014398509481984), by norm_num⟩
  | 3 => ⟨((185770143542653/1125899906842624), (498394313653/1125899906842624)), (702111/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110889256094849/2251799813685248), (7942229491447/4503599627370496)), (1405773/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103453962868761/1125899906842624), (1479182596547/281474976710656)), (528139/562949953421312), by norm_num⟩
  | 0 => ⟨((1081287191884175/1125899906842624), (23349272891569/2251799813685248)), (2120413/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081287191884175/1125899906842624), (23349272891569/2251799813685248)), (8088733677390670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038321157228793/1125899906842624), (11212040059699/562949953421312)), (8233523/2251799813685248), by norm_num⟩
  | 2 => ⟨((1914216316442709/2251799813685248), (10339905296137/281474976710656)), (3878529/562949953421312), by norm_num⟩
  | 3 => ⟨((203025464944183/281474976710656), (140636412228459/2251799813685248)), (27516381/2251799813685248), by norm_num⟩
  | 4 => ⟨((1162740624745779/2251799813685248), (1584997299007/17592186044416)), (43131733/2251799813685248), by norm_num⟩
  | 5 => ⟨((1164229251952089/4503599627370496), (419036211876067/4503599627370496)), (1634847/70368744177664), by norm_num⟩
  | 6 => ⟨((130988376172145/2251799813685248), (433301586160893/9007199254740992)), (294266657/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-626689783/8388608)), (1/8388608), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22027651/8388608), (-1273792803/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((563854511322249/9007199254740992), (-654312478050303/18014398509481984)), (126348781/9007199254740992), by norm_num⟩
  | 1 => ⟨((-818570953/4294967296), (474946265/4294967296)), (185/4294967296), by norm_num⟩
  | 2 => ⟨((1246078817/4294967296), (-90374035/536870912)), (71/1073741824), by norm_num⟩
  | 3 => ⟨((-1264571639/4294967296), (733722073/4294967296)), (145/2147483648), by norm_num⟩
  | 4 => ⟨((481252091/2147483648), (-558458329/4294967296)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((-146518279/1073741824), (680095565/8589934592)), (137/4294967296), by norm_num⟩
  | 6 => ⟨((1189541835/17179869184), (-10784199/268435456)), (35/2147483648), by norm_num⟩
  | 7 => ⟨((-64671193/2147483648), (600370027/34359738368)), (245/34359738368), by norm_num⟩
  | 8 => ⟨((787571593/68719476736), (-456960005/68719476736)), (47/17179869184), by norm_num⟩
  | 9 => ⟨((-1065679727/274877906944), (618322217/274877906944)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((40556073/34359738368), (-752998345/1099511627776)), (157/549755813888), by norm_num⟩
  | 11 => ⟨((-359196725/1099511627776), (416821883/2199023255552)), (175/2199023255552), by norm_num⟩
  | 12 => ⟨((729054993/8796093022208), (-423007859/8796093022208)), (45/2199023255552), by norm_num⟩
  | 13 => ⟨((-341480659/17592186044416), (396263667/35184372088832)), (85/17592186044416), by norm_num⟩
  | 14 => ⟨((594083159/140737488355328), (-689390643/281474976710656)), (149/140737488355328), by norm_num⟩
  | 15 => ⟨((-964639737/1125899906842624), (1093159/2199023255552)), (61/281474976710656), by norm_num⟩
  | 16 => ⟨((734216831/4503599627370496), (-426002829/4503599627370496)), (187/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-684840069583/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777919279946119/633825300114114700748351602688), (-809735235037/633825300114114700748351602688)), (184559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944393200133375/19807040628566084398385987584), (-227686486883/9903520314283042199192993792)), (25955/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236062755703945/309485009821345068724781056), (-967408509093/2475880078570760549798248448)), (220629/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770168618593923/154742504910672534362390528), (-967117212259/154742504910672534362390528)), (220643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548595579413381/9671406556917033397649408), (-453181503061/4835703278458516698824704)), (51717/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628975455893151/302231454903657293676544), (-792758387883/604462909807314587353088)), (5657/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((235803913657083/9444732965739290427392), (-643826421773/37778931862957161709568)), (294189/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296519463904071/4722366482869645213696), (-120654103837/590295810358705651712)), (110333/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810023270989869/295147905179352825856), (-2590570581/1152921504606846976)), (303453/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821724019919573/73786976294838206464), (-1656731623809/73786976294838206464)), (189687/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820689334958481/9223372036854775808), (-931064252683/4611686018427387904)), (426875/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591940163862305/1152921504606846976), (-1860012624391/1152921504606846976)), (213487/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192793387813115/144115188075855872), (-812566942329/72057594037927936)), (373715/144115188075855872), by norm_num⟩
  | 4 => ⟨((744480775183917/18014398509481984), (-608238625761/9007199254740992)), (140199/9007199254740992), by norm_num⟩
  | 3 => ⟨((742960984421743/4503599627370496), (-3032905028741/9007199254740992)), (350695/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110651946062845/2251799813685248), (-6041017465555/4503599627370496)), (21937/70368744177664), by norm_num⟩
  | 1 => ⟨((2206205287833063/2251799813685248), (-2249948745797/562949953421312)), (1054473/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161205947533549/2251799813685248), (-8877080497651/1125899906842624)), (1057499/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161205947533549/2251799813685248), (-8877080497651/1125899906842624)), (4034038545848655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2074116850457547/2251799813685248), (-17039879878895/1125899906842624)), (8186335/2251799813685248), by norm_num⟩
  | 2 => ⟨((1909938553679951/2251799813685248), (-31390625198381/1125899906842624)), (15328543/2251799813685248), by norm_num⟩
  | 3 => ⟨((1618227238178919/2251799813685248), (-53249995782161/1125899906842624)), (13428779/1125899906842624), by norm_num⟩
  | 4 => ⟨((289470352819007/562949953421312), (-153069723310049/2251799813685248)), (5142771/281474976710656), by norm_num⟩
  | 5 => ⟨((1169961036837065/4503599627370496), (-314835423953267/4503599627370496)), (95808469/4503599627370496), by norm_num⟩
  | 6 => ⟨((563854511322249/9007199254740992), (-654312478050303/18014398509481984)), (126348781/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1273792803/16777216)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile032Terms2

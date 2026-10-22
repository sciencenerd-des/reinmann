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
namespace Reinmann.XiBand97.Tile015Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26461/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26461/1280))
  have he : value ((69/80), (26461/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22364231/8388608), (-1072065077/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((301665103924877/9007199254740992), (-548809355196983/9007199254740992)), (167356973/9007199254740992), by norm_num⟩
  | 1 => ⟨((-222315703/2147483648), (808903225/4294967296)), (31/536870912), by norm_num⟩
  | 2 => ⟨((171796819/1073741824), (-1250177105/4294967296)), (385/4294967296), by norm_num⟩
  | 3 => ⟨((-708041681/4294967296), (1288116835/4294967296)), (399/4294967296), by norm_num⟩
  | 4 => ⟨((136786681/1073741824), (-995405955/4294967296)), (311/4294967296), by norm_num⟩
  | 5 => ⟨((-676501501/8589934592), (615368413/4294967296)), (193/4294967296), by norm_num⟩
  | 6 => ⟨((174257905/4294967296), (-1268086593/17179869184)), (25/1073741824), by norm_num⟩
  | 7 => ⟨((-615586951/34359738368), (559958499/17179869184)), (355/34359738368), by norm_num⟩
  | 8 => ⟨((237850675/34359738368), (-432713873/34359738368)), (69/17179869184), by norm_num⟩
  | 9 => ⟨((-653516919/274877906944), (1188921735/274877906944)), (381/274877906944), by norm_num⟩
  | 10 => ⟨((101002427/137438953472), (-735001511/549755813888)), (237/549755813888), by norm_num⟩
  | 11 => ⟨((-454113149/2199023255552), (826153045/2199023255552)), (67/549755813888), by norm_num⟩
  | 12 => ⟨((467894341/8796093022208), (-106403089/1099511627776)), (139/4398046511104), by norm_num⟩
  | 13 => ⟨((-222504811/17592186044416), (809591299/35184372088832)), (133/17592186044416), by norm_num⟩
  | 14 => ⟨((393012467/140737488355328), (-714994593/140737488355328)), (59/35184372088832), by norm_num⟩
  | 15 => ⟨((-647903051/1125899906842624), (9208661/8796093022208)), (391/1125899906842624), by norm_num⟩
  | 16 => ⟨((500673959/4503599627370496), (-910859587/4503599627370496)), (19/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-1391456302815/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888928192551799/316912650057057350374175801344), (-411277234419/158456325028528675187087900672)), (46181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888715599291157/39614081257132168796771975168), (-57822546795/1237940039285380274899124224)), (51959/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472106689728897/618970019642690137449562112), (-982716055047/1237940039285380274899124224)), (110425/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770093263710611/154742504910672534362390528), (-7675121507/604462909807314587353088)), (220877/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12097850483217/75557863725914323419136), (-1841390840959/9671406556917033397649408)), (207101/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257888961639459/604462909807314587353088), (-100661183897/37778931862957161709568)), (90621/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886330504907965/75557863725914323419136), (-653998759655/18889465931478580854784)), (294573/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648221871184033/2361183241434822606848), (-980475296309/2361183241434822606848)), (110489/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619942232981853/590295810358705651712), (-2694608927325/590295810358705651712)), (303921/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821593346385507/73786976294838206464), (-3365715881395/73786976294838206464)), (380017/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455135483273283/2305843009213693952), (-118216679405/288230376151711744)), (427679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99487016914997/72057594037927936), (-944641912867/288230376151711744)), (427879/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596331715137437/72057594037927936), (-1650670644677/72057594037927936)), (374619/144115188075855872), by norm_num⟩
  | 4 => ⟨((186095689579069/4503599627370496), (-4942217213533/36028797018963968)), (140595/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485675016293143/9007199254740992), (-3080333450537/4503599627370496)), (351883/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220804296209015/4503599627370496), (-1533770529769/562949953421312)), (1409913/4503599627370496), by norm_num⟩
  | 1 => ⟨((17230014120505/17592186044416), (-4569456526859/562949953421312)), (1060423/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079811739258605/1125899906842624), (-9012245636205/562949953421312)), (4265747/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079811739258605/1125899906842624), (-9012245636205/562949953421312)), (16272533425337981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035321615066089/1125899906842624), (-69146669794807/2251799813685248)), (8318843/2251799813685248), by norm_num⟩
  | 2 => ⟨((1901937329650719/2251799813685248), (-63583842056759/1125899906842624)), (15810089/2251799813685248), by norm_num⟩
  | 3 => ⟨((1599251391775575/2251799813685248), (-214819242874791/2251799813685248)), (28493059/2251799813685248), by norm_num⟩
  | 4 => ⟨((1115311268667625/2251799813685248), (-305133672238331/2251799813685248)), (22954271/1125899906842624), by norm_num⟩
  | 5 => ⟨((127765872113643/562949953421312), (-604528024256979/4503599627370496)), (28959305/1125899906842624), by norm_num⟩
  | 6 => ⟨((301665103924877/9007199254740992), (-548809355196983/9007199254740992)), (167356973/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1072065077/16777216)), (1/8388608), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45371695/16777216), (-1087482265/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-243743067924145/9007199254740992), (-275605603745139/4503599627370496)), (214904035/18014398509481984), by norm_num⟩
  | 1 => ⟨((364425173/4294967296), (103015873/536870912)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-571326511/4294967296), (-161502837/536870912)), (1/16777216), by norm_num⟩
  | 3 => ⟨((597130323/4294967296), (1350376563/4294967296)), (135/2147483648), by norm_num⟩
  | 4 => ⟨((-117018667/1073741824), (-1058524475/4294967296)), (107/2147483648), by norm_num⟩
  | 5 => ⟨((293529083/4294967296), (1327598947/8589934592)), (271/8589934592), by norm_num⟩
  | 6 => ⟨((-613572495/17179869184), (-693779803/8589934592)), (143/8589934592), by norm_num⟩
  | 7 => ⟨((17177259/1073741824), (1243052891/34359738368)), (129/17179869184), by norm_num⟩
  | 8 => ⟨((-215436785/34359738368), (-974396287/68719476736)), (51/17179869184), by norm_num⟩
  | 9 => ⟨((600445149/274877906944), (678936427/137438953472)), (143/137438953472), by norm_num⟩
  | 10 => ⟨((-188269229/274877906944), (-53220031/34359738368)), (181/549755813888), by norm_num⟩
  | 11 => ⟨((53665189/274877906944), (242721599/549755813888)), (13/137438953472), by norm_num⟩
  | 12 => ⟨((-224355853/4398046511104), (-507368113/4398046511104)), (219/8796093022208), by norm_num⟩
  | 13 => ⟨((432902449/35184372088832), (489492241/17592186044416)), (213/35184372088832), by norm_num⟩
  | 14 => ⟨((-96954509/35184372088832), (-877028623/140737488355328)), (193/140737488355328), by norm_num⟩
  | 15 => ⟨((324266989/562949953421312), (733311513/562949953421312)), (325/1125899906842624), by norm_num⟩
  | 16 => ⟨((-254184317/2251799813685248), (-287411751/1125899906842624)), (257/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1294236530509/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777793769664755/633825300114114700748351602688), (-3060139547559/633825300114114700748351602688)), (46251/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888644977498795/39614081257132168796771975168), (-3441846892117/39614081257132168796771975168)), (26021/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888351480920753/2475880078570760549798248448), (-3655953052411/2475880078570760549798248448)), (27653/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770017713419593/154742504910672534362390528), (-3654818052377/154742504910672534362390528)), (110637/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548453744390331/9671406556917033397649408), (-1712593198285/4835703278458516698824704)), (103749/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314456611269941/151115727451828646838272), (-187239564411/37778931862957161709568)), (90807/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943114187317237/37778931862957161709568), (-4865970154697/75557863725914323419136)), (36903/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296366672006713/4722366482869645213696), (-3647502390245/4722366482869645213696)), (55377/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619835494292077/590295810358705651712), (-5012107879987/590295810358705651712)), (152357/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821458774572845/73786976294838206464), (-97817596881/1152921504606846976)), (95277/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820388963871911/9223372036854775808), (-7036260296229/9223372036854775808)), (107261/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591637336277831/1152921504606846976), (-7028009763431/1152921504606846976)), (214707/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192525658477487/144115188075855872), (-6140237433097/144115188075855872)), (188077/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488554466823811/36028797018963968), (-4595920377603/18014398509481984)), (141267/18014398509481984), by norm_num⟩
  | 3 => ⟨((742701777262741/4503599627370496), (-11457459296575/9007199254740992)), (88475/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220238570448633/4503599627370496), (-22818134500927/4503599627370496)), (355001/2251799813685248), by norm_num⟩
  | 1 => ⟨((275567090394993/281474976710656), (-33986083050343/2251799813685248)), (1070529/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078795185208001/1125899906842624), (-33506364453389/1125899906842624)), (2163263/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078795185208001/1125899906842624), (-33506364453389/1125899906842624)), (8252193459517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032664065520345/1125899906842624), (-128418181497169/2251799813685248)), (133571/70368744177664), by norm_num⟩
  | 2 => ⟨((1886974603028775/2251799813685248), (-117783863899131/1125899906842624)), (2082039/562949953421312), by norm_num⟩
  | 3 => ⟨((778306529912857/1125899906842624), (-49350559155727/281474976710656)), (7850105/1125899906842624), by norm_num⟩
  | 4 => ⟨((251706838252937/562949953421312), (-272918487423745/1125899906842624)), (13605857/1125899906842624), by norm_num⟩
  | 5 => ⟨((317862765291991/2251799813685248), (-488110526718833/2251799813685248)), (75052247/4503599627370496), by norm_num⟩
  | 6 => ⟨((-243743067924145/9007199254740992), (-275605603745139/4503599627370496)), (214904035/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1087482265/16777216)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45987547/16777216), (-8611275/131072)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1118406567990949/18014398509481984), (-78777941950935/4503599627370496)), (407536385/18014398509481984), by norm_num⟩
  | 1 => ⟨((847424573/4294967296), (238762417/4294967296)), (155/2147483648), by norm_num⟩
  | 2 => ⟨((-1346580455/4294967296), (-379399907/4294967296)), (247/2147483648), by norm_num⟩
  | 3 => ⟨((356625431/1073741824), (25119861/268435456)), (525/4294967296), by norm_num⟩
  | 4 => ⟨((-1133374817/4294967296), (-159664541/2147483648)), (419/4294967296), by norm_num⟩
  | 5 => ⟨((1440770471/8589934592), (405938005/8589934592)), (535/8589934592), by norm_num⟩
  | 6 => ⟨((-763141019/8589934592), (-13438467/536870912)), (569/17179869184), by norm_num⟩
  | 7 => ⟨((1385887565/34359738368), (390474711/34359738368)), (519/34359738368), by norm_num⟩
  | 8 => ⟨((-1101106321/68719476736), (-310237413/68719476736)), (207/34359738368), by norm_num⟩
  | 9 => ⟨((1555277849/274877906944), (438200533/274877906944)), (587/274877906944), by norm_num⟩
  | 10 => ⟨((-988551345/549755813888), (-17407811/34359738368)), (375/549755813888), by norm_num⟩
  | 11 => ⟨((71401577/137438953472), (160939521/1099511627776)), (435/2199023255552), by norm_num⟩
  | 12 => ⟨((-302557407/2199023255552), (-170491487/4398046511104)), (231/4398046511104), by norm_num⟩
  | 13 => ⟨((36982451/1099511627776), (333434537/35184372088832)), (227/17592186044416), by norm_num⟩
  | 14 => ⟨((-1074580297/140737488355328), (-37845461/17592186044416)), (207/70368744177664), by norm_num⟩
  | 15 => ⟨((113835801/70368744177664), (16036655/35184372088832)), (353/562949953421312), by norm_num⟩
  | 16 => ⟨((-1447105213/4503599627370496), (-407722823/4503599627370496)), (563/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-3734537217577/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888865904975625/316912650057057350374175801344), (-275923095107/39614081257132168796771975168)), (92635/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888574992321311/39614081257132168796771975168), (-4965417127441/39614081257132168796771975168)), (208485/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944138371276475/1237940039285380274899124224), (-5274278213445/2475880078570760549798248448)), (55395/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884971274522355/77371252455336267181195264), (-2636308207875/77371252455336267181195264)), (221653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548382825552481/9671406556917033397649408), (-4941312704275/9671406556917033397649408)), (207877/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314440984826461/151115727451828646838272), (-1080470990947/151115727451828646838272)), (90985/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29470718071725/1180591620717411303424), (-3509876925303/37778931862957161709568)), (295847/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296289119028009/4722366482869645213696), (-657740297389/590295810358705651712)), (55503/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809863829559399/295147905179352825856), (-7230444256275/590295810358705651712)), (152737/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821322183962377/73786976294838206464), (-9031010515863/73786976294838206464)), (382153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820232834077853/9223372036854775808), (-10150206266695/9223372036854775808)), (430349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397869533079965/288230376151711744), (-1267264328393/144115188075855872)), (107721/288230376151711744), by norm_num⟩
  | 5 => ⟨((298095726730523/36028797018963968), (-2214314917661/36028797018963968)), (188813/72057594037927936), by norm_num⟩
  | 4 => ⟨((372083367279083/9007199254740992), (-13258739421613/36028797018963968)), (141911/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485115342182979/9007199254740992), (-16525981781979/9007199254740992)), (711669/9007199254740992), by norm_num⟩
  | 2 => ⟨((554906620325213/1125899906842624), (-1028434898961/140737488355328)), (714847/2251799813685248), by norm_num⟩
  | 1 => ⟨((550882558632799/562949953421312), (-12252685225907/562949953421312)), (1080239/1125899906842624), by norm_num⟩
  | 0 => ⟨((269403598566071/281474976710656), (-48305421954431/1125899906842624)), (548125/281474976710656), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269403598566071/281474976710656), (-48305421954431/1125899906842624)), (2090930939794444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((32166474176903/35184372088832), (-184935153481209/2251799813685248)), (2192539/562949953421312), by norm_num⟩
  | 2 => ⟨((29170115703149/35184372088832), (-338145118738277/2251799813685248)), (17476359/2251799813685248), by norm_num⟩
  | 3 => ⟨((1496992068806533/2251799813685248), (-560688263138365/2251799813685248)), (4278349/281474976710656), by norm_num⟩
  | 4 => ⟨((855588455927391/2251799813685248), (-745488899936791/2251799813685248)), (62552451/2251799813685248), by norm_num⟩
  | 5 => ⟨((156566231967803/4503599627370496), (-566508348505515/2251799813685248)), (88952237/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1118406567990949/18014398509481984), (-78777941950935/4503599627370496)), (407536385/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-8611275/131072)), (1/8388608), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/1048576), (-1116401477/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-472423179709549/9007199254740992), (302320567362381/9007199254740992)), (102503781/9007199254740992), by norm_num⟩
  | 1 => ⟨((362556351/2147483648), (-58003209/536870912)), (159/4294967296), by norm_num⟩
  | 2 => ⟨((-583511937/2147483648), (746820509/4294967296)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((156521039/536870912), (-400653747/2147483648)), (279/4294967296), by norm_num⟩
  | 4 => ⟨((-1007643577/4294967296), (322413665/2147483648)), (113/2147483648), by norm_num⟩
  | 5 => ⟨((324347955/2147483648), (-415123821/4294967296)), (293/8589934592), by norm_num⟩
  | 6 => ⟨((-696023861/8589934592), (445410677/8589934592)), (159/8589934592), by norm_num⟩
  | 7 => ⟨((1280236789/34359738368), (-51204345/2147483648)), (295/34359738368), by norm_num⟩
  | 8 => ⟨((-1030230813/68719476736), (659281713/68719476736)), (239/68719476736), by norm_num⟩
  | 9 => ⟨((736930013/137438953472), (-471587993/137438953472)), (43/34359738368), by norm_num⟩
  | 10 => ⟨((-474417241/274877906944), (151798319/137438953472)), (223/549755813888), by norm_num⟩
  | 11 => ⟨((555305523/1099511627776), (-88839989/274877906944)), (263/2199023255552), by norm_num⟩
  | 12 => ⟨((-595819841/4398046511104), (95321631/1099511627776)), (71/2199023255552), by norm_num⟩
  | 13 => ⟨((1180227743/35184372088832), (-377635069/17592186044416)), (283/35184372088832), by norm_num⟩
  | 14 => ⟨((-1085430443/140737488355328), (173651485/35184372088832)), (131/70368744177664), by norm_num⟩
  | 15 => ⟨((465848775/281474976710656), (-298113369/281474976710656)), (227/562949953421312), by norm_num⟩
  | 16 => ⟨((-93719335/281474976710656), (239897479/1125899906842624)), (23/281474976710656), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (837685101057/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777679632630623/633825300114114700748351602688), (3960835099317/633825300114114700748351602688)), (46295/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888516419194381/39614081257132168796771975168), (4454856662331/39614081257132168796771975168)), (104189/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888214676242761/2475880078570760549798248448), (1182985817259/618970019642690137449562112)), (110731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769880671147741/154742504910672534362390528), (1182608509879/38685626227668133590597632)), (110763/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548325015061237/9671406556917033397649408), (4433178844563/9671406556917033397649408)), (25969/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257713554992421/604462909807314587353088), (3877428970943/604462909807314587353088)), (45463/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886044456467955/75557863725914323419136), (3148909261929/37778931862957161709568)), (36955/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648114160581115/2361183241434822606848), (2360368475235/2361183241434822606848)), (55461/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619644593116535/590295810358705651712), (6486746713745/590295810358705651712)), (76305/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227652393358335/9223372036854775808), (8102037331291/73786976294838206464)), (95451/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455029502275435/2305843009213693952), (4553001817295/4611686018427387904)), (214957/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198920583643743/144115188075855872), (9095027509431/1152921504606846976)), (53799/288230376151711744), by norm_num⟩
  | 5 => ⟨((298071288678015/36028797018963968), (3972906876689/72057594037927936)), (188567/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488189887021917/36028797018963968), (2973520510779/9007199254740992)), (283391/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484941173200031/9007199254740992), (14824557104467/9007199254740992)), (355187/9007199254740992), by norm_num⟩
  | 2 => ⟨((277411747553849/562949953421312), (29520266021491/4503599627370496)), (356613/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203070766009665/2251799813685248), (10989821611339/562949953421312)), (1076989/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154465129900943/2251799813685248), (43320082163239/1125899906842624)), (2182717/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154465129900943/2251799813685248), (43320082163239/1125899906842624)), (8326404580123137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((514501050417567/562949953421312), (165790237441041/2251799813685248)), (2172351/1125899906842624), by norm_num⟩
  | 2 => ⟨((1868680717392533/2251799813685248), (151521908464491/1125899906842624)), (1072667/281474976710656), by norm_num⟩
  | 3 => ⟨((1509961963719679/2251799813685248), (502968455524863/2251799813685248)), (16552359/2251799813685248), by norm_num⟩
  | 4 => ⟨((450086160481061/1125899906842624), (674538857475483/2251799813685248)), (29592993/2251799813685248), by norm_num⟩
  | 5 => ⟨((315576486881855/4503599627370496), (539303010172215/2251799813685248)), (82778971/4503599627370496), by norm_num⟩
  | 6 => ⟨((-472423179709549/9007199254740992), (302320567362381/9007199254740992)), (102503781/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1116401477/16777216)), (1/16777216), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47145793/16777216), (-565002191/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-12849110601343/1125899906842624), (532386880292585/9007199254740992)), (371119497/18014398509481984), by norm_num⟩
  | 1 => ⟨((319394247/8589934592), (-827106405/4294967296)), (579/8589934592), by norm_num⟩
  | 2 => ⟨((-260154323/4294967296), (673698129/2147483648)), (237/2147483648), by norm_num⟩
  | 3 => ⟨((141267983/2147483648), (-1463315695/4294967296)), (517/4294967296), by norm_num⟩
  | 4 => ⟨((-230132363/4294967296), (595952975/2147483648)), (423/4294967296), by norm_num⟩
  | 5 => ⟨((149958691/4294967296), (-388334465/2147483648)), (553/8589934592), by norm_num⟩
  | 6 => ⟨((-40714991/2147483648), (843487451/8589934592)), (603/17179869184), by norm_num⟩
  | 7 => ⟨((151603853/17179869184), (-49074349/1073741824)), (563/34359738368), by norm_num⟩
  | 8 => ⟨((-123484997/34359738368), (1279111733/68719476736)), (115/17179869184), by norm_num⟩
  | 9 => ⟨((89405787/68719476736), (-926104335/137438953472)), (335/137438953472), by norm_num⟩
  | 10 => ⟨((-58258537/137438953472), (1206934931/549755813888)), (219/274877906944), by norm_num⟩
  | 11 => ⟨((276090091/2199023255552), (-714965549/1099511627776)), (521/2199023255552), by norm_num⟩
  | 12 => ⟨((-299842723/8796093022208), (1552951187/8796093022208)), (71/1099511627776), by norm_num⟩
  | 13 => ⟨((37573713/4398046511104), (-1556819965/35184372088832)), (571/35184372088832), by norm_num⟩
  | 14 => ⟨((-69953591/35184372088832), (1449219925/140737488355328)), (533/140737488355328), by norm_num⟩
  | 15 => ⟨((243109923/562949953421312), (-1259119579/562949953421312)), (465/562949953421312), by norm_num⟩
  | 16 => ⟨((-49504725/562949953421312), (1025583285/2251799813685248)), (381/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (2294587670977/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888816008157125/316912650057057350374175801344), (2712229031685/633825300114114700748351602688)), (92467/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888463108284573/39614081257132168796771975168), (3050515597043/39614081257132168796771975168)), (104043/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236019797316487/309485009821345068724781056), (3240243639895/2475880078570760549798248448)), (221131/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442456190318681/38685626227668133590597632), (202449923141/9671406556917033397649408)), (27647/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548273011294095/9671406556917033397649408), (3035639088245/9671406556917033397649408)), (25925/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257668463053643/604462909807314587353088), (2655074910341/604462909807314587353088)), (181523/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885971952552889/75557863725914323419136), (4312417799011/75557863725914323419136)), (36883/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296174616591489/4722366482869645213696), (808123819193/1180591620717411303424)), (3459/73786976294838206464), by norm_num⟩
  | 9 => ⟨((404892960508703/147573952589676412928), (4441728495919/590295810358705651712)), (38065/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821129844418675/73786976294838206464), (5547735105291/73786976294838206464)), (47605/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820019789601299/9223372036854775808), (6235122188309/9223372036854775808)), (107177/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591269250396631/1152921504606846976), (6227530341801/1152921504606846976)), (429037/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298051201323851/36028797018963968), (680069885969/18014398509481984)), (187889/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488075624802651/36028797018963968), (2035951460891/9007199254740992)), (564409/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484809254194679/9007199254740992), (1268751361823/1125899906842624)), (176703/2251799813685248), by norm_num⟩
  | 2 => ⟨((138691416938807/281474976710656), (10105513009497/2251799813685248)), (1417535/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202804433943139/2251799813685248), (15047449917063/1125899906842624)), (534029/562949953421312), by norm_num⟩
  | 0 => ⟨((134640679832579/140737488355328), (59308329280513/2251799813685248)), (2155843/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((134640679832579/140737488355328), (59308329280513/2251799813685248)), (8223888401511764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((64355179026329/70368744177664), (113478133898507/2251799813685248)), (8476929/2251799813685248), by norm_num⟩
  | 2 => ⟨((1877657992758421/2251799813685248), (103780530801773/1125899906842624)), (16359397/2251799813685248), by norm_num⟩
  | 3 => ⟨((386637160451685/562949953421312), (173074304357233/1125899906842624)), (15149183/1125899906842624), by norm_num⟩
  | 4 => ⟨((1008967950148737/2251799813685248), (118868395275895/562949953421312)), (12733289/562949953421312), by norm_num⟩
  | 5 => ⟨((703385081823777/4503599627370496), (852185174828361/4503599627370496)), (67152767/2251799813685248), by norm_num⟩
  | 6 => ⟨((-12849110601343/1125899906842624), (532386880292585/9007199254740992)), (371119497/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-565002191/8388608)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47691909/16777216), (-1143093845/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((583545994152605/18014398509481984), (872560040977885/18014398509481984)), (134702479/18014398509481984), by norm_num⟩
  | 1 => ⟨((-458543873/4294967296), (-685647857/4294967296)), (107/4294967296), by norm_num⟩
  | 2 => ⟨((755642901/4294967296), (564945871/2147483648)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-830158577/4294967296), (-1241312953/4294967296)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((684016811/4294967296), (63924453/268435456)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((-450881565/4294967296), (-168547655/1073741824)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((123836007/2147483648), (185168525/2147483648)), (123/8589934592), by norm_num⟩
  | 7 => ⟨((-116612365/4294967296), (-348734429/8589934592)), (59/8589934592), by norm_num⟩
  | 8 => ⟨((768670663/68719476736), (287342947/17179869184)), (197/68719476736), by norm_num⟩
  | 9 => ⟨((-562980691/137438953472), (-420904657/68719476736)), (73/68719476736), by norm_num⟩
  | 10 => ⟨((371098503/274877906944), (277446617/137438953472)), (195/549755813888), by norm_num⟩
  | 11 => ⟨((-222378205/549755813888), (-332515923/549755813888)), (59/549755813888), by norm_num⟩
  | 12 => ⟨((488614857/4398046511104), (365306079/2199023255552)), (33/1099511627776), by norm_num⟩
  | 13 => ⟨((-247753055/8796093022208), (-740916457/17592186044416)), (17/2199023255552), by norm_num⟩
  | 14 => ⟨((466602087/70368744177664), (348848539/35184372088832)), (129/70368744177664), by norm_num⟩
  | 15 => ⟨((-820183659/562949953421312), (-613198867/281474976710656)), (229/562949953421312), by norm_num⟩
  | 16 => ⟨((675797885/2251799813685248), (252625429/562949953421312)), (95/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (639149724939/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777584620954113/633825300114114700748351602688), (1510883390065/633825300114114700748351602688)), (46175/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888409950008125/39614081257132168796771975168), (1699328617543/39614081257132168796771975168)), (103903/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051057240507/1237940039285380274899124224), (1805013361373/2475880078570760549798248448)), (13801/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442442185157299/38685626227668133590597632), (451106241773/38685626227668133590597632)), (27605/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548220750344309/9671406556917033397649408), (845511749257/4835703278458516698824704)), (25883/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257622992888349/604462909807314587353088), (739510473295/302231454903657293676544)), (90605/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471474636771571/18889465931478580854784), (2402238509227/75557863725914323419136)), (147257/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296119985091163/4722366482869645213696), (28135238939/73786976294838206464)), (110465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619497409494001/590295810358705651712), (2474238860569/590295810358705651712)), (37981/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910518915368149/36893488147419103232), (3090307367985/73786976294838206464)), (94979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819917683623473/9223372036854775808), (434146711577/1152921504606846976)), (13361/576460752303423488), by norm_num⟩
  | 6 => ⟨((795584451070709/576460752303423488), (3468901038353/1152921504606846976)), (53467/288230376151711744), by norm_num⟩
  | 5 => ⟨((596059486228425/72057594037927936), (1515244246307/72057594037927936)), (93619/72057594037927936), by norm_num⟩
  | 4 => ⟨((371987701365327/9007199254740992), (567018741507/4503599627370496)), (281065/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484660076284715/9007199254740992), (353340983755/562949953421312)), (21981/562949953421312), by norm_num⟩
  | 2 => ⟨((2218784730062533/4503599627370496), (2814217264379/1125899906842624)), (352245/2251799813685248), by norm_num⟩
  | 1 => ⟨((550609531928589/562949953421312), (8380365042559/1125899906842624)), (264873/562949953421312), by norm_num⟩
  | 0 => ⟨((538429527175007/562949953421312), (33026349110159/2251799813685248)), (133131/140737488355328), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538429527175007/562949953421312), (33026349110159/2251799813685248)), (507854462206792787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1029712082713381/1125899906842624), (7896954883657/281474976710656)), (2068557/1125899906842624), by norm_num⟩
  | 2 => ⟨((235213889020031/281474976710656), (115556842108959/2251799813685248)), (1949871/562949953421312), by norm_num⟩
  | 3 => ⟨((1566517282944507/2251799813685248), (193129595766961/2251799813685248)), (6917871/1125899906842624), by norm_num⟩
  | 4 => ⟨((134152542241735/281474976710656), (67177563426897/562949953421312)), (21623611/2251799813685248), by norm_num⟩
  | 5 => ⟨((239718621243793/1125899906842624), (512275216540481/4503599627370496)), (3221577/281474976710656), by norm_num⟩
  | 6 => ⟨((583545994152605/18014398509481984), (872560040977885/18014398509481984)), (134702479/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1143093845/16777216)), (1/16777216), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile015Terms3

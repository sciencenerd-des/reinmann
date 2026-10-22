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
namespace Reinmann.XiBand97.Tile000Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (18227/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (18227/1280))
  have he : value ((69/80), (18227/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1049855587/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((41961379165749/281474976710656), (172534572878683/9007199254740992)), (93967185/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1406838587/4294967296), (-180767633/4294967296)), (101/4294967296), by norm_num⟩
  | 2 => ⟨((96598135/268435456), (198593543/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-1131988247/4294967296), (-72725769/2147483648)), (85/4294967296), by norm_num⟩
  | 4 => ⟨((1243616199/8589934592), (159794847/8589934592)), (95/8589934592), by norm_num⟩
  | 5 => ⟨((-1093001631/17179869184), (-70221033/8589934592)), (85/17179869184), by norm_num⟩
  | 6 => ⟨((800523349/34359738368), (205721839/68719476736)), (127/68719476736), by norm_num⟩
  | 7 => ⟨((-125637827/17179869184), (-129147737/137438953472)), (41/68719476736), by norm_num⟩
  | 8 => ⟨((552109043/274877906944), (141883291/549755813888)), (23/137438953472), by norm_num⟩
  | 9 => ⟨((-539158915/1099511627776), (-138555313/2199023255552)), (23/549755813888), by norm_num⟩
  | 10 => ⟨((1895445151/17592186044416), (243549711/17592186044416)), (41/4398046511104), by norm_num⟩
  | 11 => ⟨((-1514443153/70368744177664), (-12162123/4398046511104)), (67/35184372088832), by norm_num⟩
  | 12 => ⟨((1109190573/281474976710656), (17815277/35184372088832)), (101/281474976710656), by norm_num⟩
  | 13 => ⟨((-1499778947/2251799813685248), (-192709733/2251799813685248)), (139/2251799813685248), by norm_num⟩
  | 14 => ⟨((117691113/1125899906842624), (241958035/18014398509481984)), (177/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1103333573/72057594037927936), (-70884819/36028797018963968)), (53/36028797018963968), by norm_num⟩
  | 16 => ⟨((606067911/288230376151711744), (155749867/576460752303423488)), (119/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (166463180797/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889522919129327/316912650057057350374175801344), (98529441913/316912650057057350374175801344)), (23055/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890053547815131/39614081257132168796771975168), (110827221593/19807040628566084398385987584)), (103749/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944924051963551/1237940039285380274899124224), (117731162887/1237940039285380274899124224)), (55117/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771514355284415/154742504910672534362390528), (235411132939/154742504910672534362390528)), (27559/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549856865960841/9671406556917033397649408), (220643560481/9671406556917033397649408)), (25837/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259054196034145/604462909807314587353088), (753940455/2361183241434822606848)), (1413/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((944111753067155/37778931862957161709568), (156768671941/37778931862957161709568)), (73477/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648931525896177/2361183241434822606848), (235063895787/4722366482869645213696)), (110219/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810946533086121/295147905179352825856), (161534059985/295147905179352825856)), (151555/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912015406127699/36893488147419103232), (403618168099/73786976294838206464)), (189451/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455820650920895/2305843009213693952), (113443072297/2305843009213693952)), (213141/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594531093782077/1152921504606846976), (453399901767/1152921504606846976)), (106577/576460752303423488), by norm_num⟩
  | 5 => ⟨((298764455774729/36028797018963968), (198153195153/72057594037927936)), (46631/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492352953405983/36028797018963968), (593623567145/36028797018963968)), (279813/36028797018963968), by norm_num⟩
  | 3 => ⟨((745076025415615/4503599627370496), (370284369735/4503599627370496)), (349815/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229736602561975/4503599627370496), (738382277885/2251799813685248)), (699781/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218785935791737/2251799813685248), (1102123390461/1125899906842624)), (525025/1125899906842624), by norm_num⟩
  | 0 => ⟨((546523716467275/562949953421312), (4365086338805/2251799813685248)), (2101649/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546523716467275/562949953421312), (4365086338805/2251799813685248)), (8017154702193450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1061149325876197/1125899906842624), (8475436205601/2251799813685248)), (127775/70368744177664), by norm_num⟩
  | 2 => ⟨((2000213210267511/2251799813685248), (15976026574691/2251799813685248)), (3869043/1125899906842624), by norm_num⟩
  | 3 => ⟨((1776622250694769/2251799813685248), (14191074716355/1125899906842624)), (3464217/562949953421312), by norm_num⟩
  | 4 => ⟨((1401359506328837/2251799813685248), (349889271755/17592186044416)), (5553715/562949953421312), by norm_num⟩
  | 5 => ⟨((871215409013989/2251799813685248), (111486009958831/4503599627370496)), (14266773/1125899906842624), by norm_num⟩
  | 6 => ⟨((41961379165749/281474976710656), (172534572878683/9007199254740992)), (93967185/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1049855587/33554432)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1100197881/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((243500360006151/9007199254740992), (-605992008725853/4503599627370496)), (92952625/4503599627370496), by norm_num⟩
  | 1 => ⟨((-267353201/4294967296), (332676927/1073741824)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((76950437/1073741824), (-766016933/2147483648)), (241/4294967296), by norm_num⟩
  | 3 => ⟨((-59061643/1073741824), (1175879447/4294967296)), (187/4294967296), by norm_num⟩
  | 4 => ⟨((135994459/4294967296), (-1353781243/8589934592)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-250511051/17179869184), (311719651/4294967296)), (203/17179869184), by norm_num⟩
  | 6 => ⟨((192274337/34359738368), (-119626837/4294967296)), (79/17179869184), by norm_num⟩
  | 7 => ⟨((-252987441/137438953472), (629602221/68719476736)), (105/68719476736), by norm_num⟩
  | 8 => ⟨((291262555/549755813888), (-1449712689/549755813888)), (61/137438953472), by norm_num⟩
  | 9 => ⟨((-298069697/2199023255552), (1483594145/2199023255552)), (63/549755813888), by norm_num⟩
  | 10 => ⟨((17158271/549755813888), (-1366440705/8796093022208)), (117/4398046511104), by norm_num⟩
  | 11 => ⟨((-229866933/35184372088832), (572062909/17592186044416)), (99/17592186044416), by norm_num⟩
  | 12 => ⟨((176429391/140737488355328), (-439074509/70368744177664)), (307/281474976710656), by norm_num⟩
  | 13 => ⟨((-124998057/562949953421312), (1244315593/1125899906842624)), (55/281474976710656), by norm_num⟩
  | 14 => ⟨((328935615/9007199254740992), (-818612153/4503599627370496)), (73/2251799813685248), by norm_num⟩
  | 15 => ⟨((-50493483/9007199254740992), (1005292875/36028797018963968)), (181/36028797018963968), by norm_num⟩
  | 16 => ⟨((232531083/288230376151711744), (-578693097/144115188075855872)), (211/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-446966895467/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889451671791087/316912650057057350374175801344), (-529039463451/158456325028528675187087900672)), (92409/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889893133421121/39614081257132168796771975168), (-2380261116957/39614081257132168796771975168)), (103973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889677522139851/2475880078570760549798248448), (-2528514830263/2475880078570760549798248448)), (110487/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771343614458275/154742504910672534362390528), (-2527938306027/154742504910672534362390528)), (110505/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549696627572783/9671406556917033397649408), (-2369329761619/9671406556917033397649408)), (1619/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258913818710769/604462909807314587353088), (-1036275658709/302231454903657293676544)), (90683/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943997538441707/37778931862957161709568), (-3366748345309/75557863725914323419136)), (73697/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297691453541655/4722366482869645213696), (-1262028765535/2361183241434822606848)), (6911/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621656670085541/590295810358705651712), (-3468948749135/590295810358705651712)), (38023/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227966830663881/9223372036854775808), (-4333741629929/73786976294838206464)), (47547/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911474246780533/4611686018427387904), (-4872100406317/9223372036854775808)), (13379/576460752303423488), by norm_num⟩
  | 6 => ⟨((797097916482971/576460752303423488), (-2433952368373/576460752303423488)), (214191/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597381589183613/72057594037927936), (-1063675156175/36028797018963968)), (93781/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491908410793087/36028797018963968), (-3186314580349/18014398509481984)), (140815/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489591882299513/9007199254740992), (-7949321415363/9007199254740992)), (352541/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228602862081013/4503599627370496), (-3962334979297/1125899906842624)), (353299/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217052051608903/2251799813685248), (-23651074820135/2251799813685248)), (1063695/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091247704103377/1125899906842624), (-23406169605033/1125899906842624)), (1071319/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091247704103377/1125899906842624), (-23406169605033/1125899906842624)), (4086757664207076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2114350832967403/2251799813685248), (-45371579992353/1125899906842624)), (2121237/1125899906842624), by norm_num⟩
  | 2 => ⟨((1981634911179393/2251799813685248), (-21301058239471/281474976710656)), (4154479/1125899906842624), by norm_num⟩
  | 3 => ⟨((1730987742453925/2251799813685248), (-299926630393097/2251799813685248)), (15881731/2251799813685248), by norm_num⟩
  | 4 => ⟨((161335532761585/281474976710656), (-57639373368219/281474976710656)), (28647695/2251799813685248), by norm_num⟩
  | 5 => ⟨((40335480323221/140737488355328), (-264301405946001/1125899906842624)), (44573245/2251799813685248), by norm_num⟩
  | 6 => ⟨((243500360006151/9007199254740992), (-605992008725853/4503599627370496)), (92952625/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1100197881/33554432)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-572869013/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1043427237214389/9007199254740992), (-227910860919505/4503599627370496)), (202322697/9007199254740992), by norm_num⟩
  | 1 => ⟨((37283141/134217728), (521189095/4294967296)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((-1430417081/4294967296), (-312439217/2147483648)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((1143330119/4294967296), (124866087/1073741824)), (57/1073741824), by norm_num⟩
  | 4 => ⟨((-85674559/536870912), (-37426975/536870912)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((10271931/134217728), (574374185/17179869184)), (267/17179869184), by norm_num⟩
  | 6 => ⟨((-525461649/17179869184), (-459096381/34359738368)), (215/34359738368), by norm_num⟩
  | 7 => ⟨((720001145/68719476736), (314532869/68719476736)), (297/137438953472), by norm_num⟩
  | 8 => ⟨((-863243671/274877906944), (-47138555/34359738368)), (45/68719476736), by norm_num⟩
  | 9 => ⟨((919985741/1099511627776), (200948121/549755813888)), (97/549755813888), by norm_num⟩
  | 10 => ⟨((-110301473/549755813888), (-48185255/549755813888)), (47/1099511627776), by norm_num⟩
  | 11 => ⟨((769429471/17592186044416), (336125659/17592186044416)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((-153750941/17592186044416), (-537329419/140737488355328)), (67/35184372088832), by norm_num⟩
  | 13 => ⟨((56719793/35184372088832), (198224565/281474976710656)), (25/70368744177664), by norm_num⟩
  | 14 => ⟨((-310875711/1125899906842624), (-271612427/2251799813685248)), (277/4503599627370496), by norm_num⟩
  | 15 => ⟨((795143891/18014398509481984), (43419877/2251799813685248)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((-953335889/144115188075855872), (-416465271/144115188075855872)), (217/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-3555774827209/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778769526151545/633825300114114700748351602688), (-4208119328011/633825300114114700748351602688)), (92615/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944871107444241/19807040628566084398385987584), (-1183313696365/9903520314283042199192993792)), (52109/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944758341091337/1237940039285380274899124224), (-5028019552671/2475880078570760549798248448)), (55381/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221397778099035/19342813113834066795298816), (-5026822999155/154742504910672534362390528)), (110797/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549544741084509/9671406556917033397649408), (-2355687697683/4835703278458516698824704)), (103909/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258780334794789/604462909807314587353088), (-4121182497435/604462909807314587353088)), (45479/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471944268219239/18889465931478580854784), (-6694538893063/75557863725914323419136)), (73937/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648763497701703/2361183241434822606848), (-1254704937021/1180591620717411303424)), (110967/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810714494897503/295147905179352825856), (-1724372684633/147573952589676412928)), (152677/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823447722467705/73786976294838206464), (-1077098143725/9223372036854775808)), (95497/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911311258448751/4611686018427387904), (-4843451431417/4611686018427387904)), (215071/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199233234766679/144115188075855872), (-302443144433/36028797018963968)), (107663/576460752303423488), by norm_num⟩
  | 5 => ⟨((597235001315195/72057594037927936), (-8458600064403/144115188075855872)), (23587/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491459742095505/36028797018963968), (-6334147756481/18014398509481984)), (8863/1125899906842624), by norm_num⟩
  | 3 => ⟨((744507759819607/4503599627370496), (-7900543513329/4503599627370496)), (355523/9007199254740992), by norm_num⟩
  | 2 => ⟨((556850946119895/1125899906842624), (-15749714946121/2251799813685248)), (44629/281474976710656), by norm_num⟩
  | 1 => ⟨((1107569175479385/1125899906842624), (-23496323033401/1125899906842624)), (269663/562949953421312), by norm_num⟩
  | 0 => ⟨((272276554239143/281474976710656), (-46480738853839/1125899906842624)), (273455/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272276554239143/281474976710656), (-46480738853839/1125899906842624)), (1043148041845226199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((525798024110927/562949953421312), (-89923555987161/1125899906842624)), (2206463/1125899906842624), by norm_num⟩
  | 2 => ⟨((975013849848277/1125899906842624), (-83989043380721/562949953421312)), (1118537/281474976710656), by norm_num⟩
  | 3 => ⟨((1638574377984845/2251799813685248), (-290933430348555/1125899906842624)), (18168277/2251799813685248), by norm_num⟩
  | 4 => ⟨((130248975416853/281474976710656), (-423408920962825/1125899906842624)), (8957633/562949953421312), by norm_num⟩
  | 5 => ⟨((327423830993239/4503599627370496), (-783708431665719/2251799813685248)), (120218601/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1043427237214389/9007199254740992), (-227910860919505/4503599627370496)), (202322697/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-572869013/16777216)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-148414115/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-715093859444815/9007199254740992), (194366757773705/2251799813685248)), (6006613/281474976710656), by norm_num⟩
  | 1 => ⟨((847311729/4294967296), (-921217439/4294967296)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((-526372637/2147483648), (572284835/2147483648)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((217997811/1073741824), (-474024797/2147483648)), (243/4294967296), by norm_num⟩
  | 4 => ⟨((-270852105/2147483648), (588953685/4294967296)), (19/536870912), by norm_num⟩
  | 5 => ⟨((538433757/8589934592), (-585397971/8589934592)), (153/8589934592), by norm_num⟩
  | 6 => ⟨((-891971749/34359738368), (484886437/17179869184)), (1/134217728), by norm_num⟩
  | 7 => ⟨((633276151/68719476736), (-688512875/68719476736)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((-786816059/274877906944), (855445111/274877906944)), (231/274877906944), by norm_num⟩
  | 9 => ⟨((868961981/1099511627776), (-944756109/1099511627776)), (129/549755813888), by norm_num⟩
  | 10 => ⟨((-431857881/2199023255552), (939052295/4398046511104)), (259/4398046511104), by norm_num⟩
  | 11 => ⟨((780455651/17592186044416), (-212132481/4398046511104)), (59/4398046511104), by norm_num⟩
  | 12 => ⟨((-323226573/35184372088832), (702839217/70368744177664)), (99/35184372088832), by norm_num⟩
  | 13 => ⟨((988538905/562949953421312), (-1074762981/562949953421312)), (305/562949953421312), by norm_num⟩
  | 14 => ⟨((-701836257/2251799813685248), (763053051/2251799813685248)), (219/2251799813685248), by norm_num⟩
  | 15 => ⟨((232533011/4503599627370496), (-1011261653/18014398509481984)), (293/18014398509481984), by norm_num⟩
  | 16 => ⟨((-577822825/72057594037927936), (628222701/72057594037927936)), (23/9007199254740992), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (753700683741/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((13895753952773/4951760157141521099596496896), (445932285449/79228162514264337593543950336)), (11569/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889615242956461/39614081257132168796771975168), (4012626040729/39614081257132168796771975168)), (104143/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889382000159741/2475880078570760549798248448), (4262481576109/2475880078570760549798248448)), (55339/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771047796484797/154742504910672534362390528), (4261431456609/154742504910672534362390528)), (110707/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387354745992985/2417851639229258349412352), (3993976463975/9671406556917033397649408)), (25955/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314667641645457/151115727451828646838272), (1746807066329/302231454903657293676544)), (45437/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943799602021761/37778931862957161709568), (5675032366363/75557863725914323419136)), (147727/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648697017438047/2361183241434822606848), (2127222769403/2361183241434822606848)), (110847/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621246885196299/590295810358705651712), (5846891929441/590295810358705651712)), (76249/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227902645594823/9223372036854775808), (7304160649137/73786976294838206464)), (190747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822369113035325/9223372036854775808), (2052764747739/2305843009213693952)), (214763/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593614313420713/1152921504606846976), (8203411125493/1152921504606846976)), (214979/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597125974350161/72057594037927936), (7169386812107/144115188075855872)), (188349/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491136781970105/36028797018963968), (10736899192083/36028797018963968)), (2211/281474976710656), by norm_num⟩
  | 3 => ⟨((372154752302065/2251799813685248), (3347772637523/2251799813685248)), (354611/9007199254740992), by norm_num⟩
  | 2 => ⟨((139164515400041/281474976710656), (13346107131385/2251799813685248)), (177945/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107017224412807/1125899906842624), (19906935878409/1125899906842624)), (268519/562949953421312), by norm_num⟩
  | 0 => ⟨((544054110259137/562949953421312), (19683187950719/562949953421312)), (135867/140737488355328), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544054110259137/562949953421312), (19683187950719/562949953421312)), (518291473925542787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((525104310259575/562949953421312), (76090027133033/1125899906842624)), (2176913/1125899906842624), by norm_num⟩
  | 2 => ⟨((1948927160781775/2251799813685248), (283898779793813/2251799813685248)), (8710737/2251799813685248), by norm_num⟩
  | 3 => ⟨((1650998698139225/2251799813685248), (15357105666385/70368744177664)), (2159335/281474976710656), by norm_num⟩
  | 4 => ⟨((1103248972241627/2251799813685248), (720619978619315/2251799813685248)), (4108905/281474976710656), by norm_num⟩
  | 5 => ⟨((309914379122713/2251799813685248), (44132655906889/140737488355328)), (26624407/1125899906842624), by norm_num⟩
  | 6 => ⟨((-715093859444815/9007199254740992), (194366757773705/2251799813685248)), (6006613/281474976710656), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-148414115/4194304)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-306389529/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((190211596069465/4503599627370496), (909500346089977/9007199254740992)), (137356137/9007199254740992), by norm_num⟩
  | 1 => ⟨((-465281593/4294967296), (-556188185/2147483648)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((298355931/2147483648), (44581079/134217728)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((-510178569/4294967296), (-19058035/67108864)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((81786387/1073741824), (391063157/2147483648)), (31/1073741824), by norm_num⟩
  | 5 => ⟨((-335644705/8589934592), (-802445755/8589934592)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((286970557/17179869184), (1372155149/34359738368)), (223/34359738368), by norm_num⟩
  | 7 => ⟨((-420608541/68719476736), (-125696731/8589934592)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((134854951/68719476736), (644811499/137438953472)), (215/274877906944), by norm_num⟩
  | 9 => ⟨((-153731609/274877906944), (-1470141191/1099511627776)), (31/137438953472), by norm_num⟩
  | 10 => ⟨((630902067/4398046511104), (754167541/2199023255552)), (257/4398046511104), by norm_num⟩
  | 11 => ⟨((-294223973/8796093022208), (-1406837491/17592186044416)), (121/8796093022208), by norm_num⟩
  | 12 => ⟨((125778265/17592186044416), (601411153/35184372088832)), (209/70368744177664), by norm_num⟩
  | 13 => ⟨((-99266117/70368744177664), (-949285631/281474976710656)), (167/281474976710656), by norm_num⟩
  | 14 => ⟨((581971573/2251799813685248), (173919255/281474976710656)), (247/2251799813685248), by norm_num⟩
  | 15 => ⟨((-398060697/9007199254740992), (-475833687/4503599627370496)), (171/9007199254740992), by norm_num⟩
  | 16 => ⟨((510502765/72057594037927936), (610244655/36028797018963968)), (111/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (382522906925/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778555157565679/633825300114114700748351602688), (1810372530523/633825300114114700748351602688)), (92379/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889501533472589/39614081257132168796771975168), (2036275303329/39614081257132168796771975168)), (103937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944630791852421/1237940039285380274899124224), (270381776393/309485009821345068724781056)), (110447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442731957383985/38685626227668133590597632), (540626267111/38685626227668133590597632)), (55231/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774653496128649/4835703278458516698824704), (2026765216533/9671406556917033397649408)), (51787/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258573050793675/604462909807314587353088), (1772836480699/604462909807314587353088)), (90643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235930204309305/9444732965739290427392), (2879766426823/75557863725914323419136)), (36831/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162159579858829/590295810358705651712), (2158869000171/4722366482869645213696)), (13815/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621086733748719/590295810358705651712), (2966892469165/590295810358705651712)), (152007/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455755718797383/18446744073709551616), (463286047371/9223372036854775808)), (190071/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822148645598459/9223372036854775808), (4166376792297/9223372036854775808)), (106959/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593397100677575/1152921504606846976), (32518618451/9007199254740992)), (214027/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194065541228999/144115188075855872), (3637597119699/144115188075855872)), (187397/144115188075855872), by norm_num⟩
  | 4 => ⟨((745432229259423/18014398509481984), (2723715546591/18014398509481984)), (140671/18014398509481984), by norm_num⟩
  | 3 => ⟨((744145657217629/4503599627370496), (6793627149567/9007199254740992)), (352111/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226014809718459/4503599627370496), (6770187112469/2251799813685248)), (705521/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106601281225593/1125899906842624), (20193728198989/2251799813685248)), (1061543/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174926074983273/2251799813685248), (39922320368987/2251799813685248)), (2136191/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174926074983273/2251799813685248), (39922320368987/2251799813685248)), (8148921975142668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099968927628427/2251799813685248), (19279710171537/562949953421312)), (2101137/1125899906842624), by norm_num⟩
  | 2 => ⟨((488933580446561/562949953421312), (143837980793327/2251799813685248)), (31741/8796093022208), by norm_num⟩
  | 3 => ⟨((422351861561365/562949953421312), (62463118192011/562949953421312)), (15152757/2251799813685248), by norm_num⟩
  | 4 => ⟨((1239751084583541/2251799813685248), (374902445050273/2251799813685248)), (26099243/2251799813685248), by norm_num⟩
  | 5 => ⟨((1240279797462123/4503599627370496), (206406319975415/1125899906842624)), (4678617/281474976710656), by norm_num⟩
  | 6 => ⟨((190211596069465/4503599627370496), (909500346089977/9007199254740992)), (137356137/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-306389529/8388608)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-315241909/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1836470434946885/18014398509481984), (55056346777845/4503599627370496)), (128156015/18014398509481984), by norm_num⟩
  | 1 => ⟨((-577753873/2147483648), (-138565879/4294967296)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((1524725593/4294967296), (182841649/4294967296)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((-1341279417/4294967296), (-80421599/2147483648)), (49/2147483648), by norm_num⟩
  | 4 => ⟨((884928319/4294967296), (106118605/4294967296)), (33/2147483648), by norm_num⟩
  | 5 => ⟨((-1868301253/17179869184), (-112021233/8589934592)), (71/8589934592), by norm_num⟩
  | 6 => ⟨((821759019/17179869184), (197086971/34359738368)), (127/34359738368), by norm_num⟩
  | 7 => ⟨((-1239239521/68719476736), (-37151701/17179869184)), (49/34359738368), by norm_num⟩
  | 8 => ⟨((817606035/137438953472), (98045469/137438953472)), (33/68719476736), by norm_num⟩
  | 9 => ⟨((-479490933/274877906944), (-114998939/549755813888)), (79/549755813888), by norm_num⟩
  | 10 => ⟨((1012323249/2199023255552), (121395517/2199023255552)), (85/2199023255552), by norm_num⟩
  | 11 => ⟨((-971483305/8796093022208), (-116498083/8796093022208)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((1709200091/70368744177664), (204963413/70368744177664)), (37/17592186044416), by norm_num⟩
  | 13 => ⟨((-86743789/17592186044416), (-166433907/281474976710656)), (61/140737488355328), by norm_num⟩
  | 14 => ⟨((261624951/281474976710656), (31373473/281474976710656)), (93/1125899906842624), by norm_num⟩
  | 15 => ⟨((-368236397/2251799813685248), (-176632307/9007199254740992)), (133/9007199254740992), by norm_num⟩
  | 16 => ⟨((485898481/18014398509481984), (7283481/2251799813685248)), (89/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (155463879763/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778458387752007/633825300114114700748351602688), (11495138433/39614081257132168796771975168)), (92219/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889392786352835/39614081257132168796771975168), (206871597735/39614081257132168796771975168)), (103747/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889146194391321/2475880078570760549798248448), (109875028929/1237940039285380274899124224)), (110233/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770812613892127/154742504910672534362390528), (219692690671/154742504910672534362390528)), (55117/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549199162001039/9671406556917033397649408), (51475241513/2417851639229258349412352)), (103347/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258478883600651/604462909807314587353088), (180102437685/604462909807314587353088)), (45215/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943644479019953/37778931862957161709568), (146276155053/37778931862957161709568)), (146951/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297162433369159/4722366482869645213696), (219314400951/4722366482869645213696)), (110217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620930191137547/590295810358705651712), (301395169753/590295810358705651712)), (37/144115188075855872), by norm_num⟩
  | 8 => ⟨((911413965480781/36893488147419103232), (188250465359/36893488147419103232)), (94723/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821930341190215/9223372036854775808), (13225926503/288230376151711744)), (13321/576460752303423488), by norm_num⟩
  | 6 => ⟨((796590026952691/576460752303423488), (211406338997/576460752303423488)), (53287/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193877037158673/144115188075855872), (369492556237/144115188075855872)), (93259/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490584518674035/36028797018963968), (553303144447/36028797018963968)), (69951/9007199254740992), by norm_num⟩
  | 3 => ⟨((743973150679347/4503599627370496), (344997291275/4503599627370496)), (174901/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112669726012633/2251799813685248), (1375098533925/4503599627370496)), (174937/1125899906842624), by norm_num⟩
  | 1 => ⟨((2212225964313407/2251799813685248), (2050464557983/2251799813685248)), (131249/281474976710656), by norm_num⟩
  | 0 => ⟨((2173117242223365/2251799813685248), (506556909637/281474976710656)), (525377/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173117242223365/2251799813685248), (506556909637/281474976710656)), (2004154207469749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2097176710538089/2251799813685248), (7821708113195/2251799813685248)), (4063719/2251799813685248), by norm_num⟩
  | 2 => ⟨((1953143858248985/2251799813685248), (14569238341639/2251799813685248)), (7597587/2251799813685248), by norm_num⟩
  | 3 => ⟨((211750543117055/281474976710656), (25273843805651/2251799813685248)), (6639077/1125899906842624), by norm_num⟩
  | 4 => ⟨((318524312868143/562949953421312), (38026471944635/2251799813685248)), (20276085/2251799813685248), by norm_num⟩
  | 5 => ⟨((720258427851575/2251799813685248), (86063464600021/4503599627370496)), (47259499/4503599627370496), by norm_num⟩
  | 6 => ⟨((1836470434946885/18014398509481984), (55056346777845/4503599627370496)), (128156015/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-315241909/8388608)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1293933111/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((283237848256307/4503599627370496), (-662133314866741/9007199254740992)), (104089219/9007199254740992), by norm_num⟩
  | 1 => ⟨((-731489479/4294967296), (427506031/2147483648)), (17/536870912), by norm_num⟩
  | 2 => ⟨((247613779/1073741824), (-578853897/2147483648)), (47/1073741824), by norm_num⟩
  | 3 => ⟨((-13969803/67108864), (130630451/536870912)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((605294845/4294967296), (-353753819/2147483648)), (59/2147483648), by norm_num⟩
  | 5 => ⟨((-655667531/8589934592), (47899155/536870912)), (65/4294967296), by norm_num⟩
  | 6 => ⟨((147965049/4294967296), (-345902177/8589934592)), (119/17179869184), by norm_num⟩
  | 7 => ⟨((-228969589/17179869184), (267634417/17179869184)), (187/68719476736), by norm_num⟩
  | 8 => ⟨((620061141/137438953472), (-724767437/137438953472)), (129/137438953472), by norm_num⟩
  | 9 => ⟨((-746291865/549755813888), (436157023/274877906944)), (157/549755813888), by norm_num⟩
  | 10 => ⟨((404199167/1099511627776), (-944908091/2199023255552)), (43/549755813888), by norm_num⟩
  | 11 => ⟨((-199016661/2199023255552), (930494017/8796093022208)), (43/2199023255552), by norm_num⟩
  | 12 => ⟨((718596145/35184372088832), (-839941503/35184372088832)), (157/35184372088832), by norm_num⟩
  | 13 => ⟨((-299383759/70368744177664), (699878079/140737488355328)), (133/140737488355328), by norm_num⟩
  | 14 => ⟨((926567141/1125899906842624), (-1083031413/1125899906842624)), (13/70368744177664), by norm_num⟩
  | 15 => ⟨((-334558711/2251799813685248), (782107583/4503599627370496)), (19/562949953421312), by norm_num⟩
  | 16 => ⟨((113250223/4503599627370496), (-1058993299/36028797018963968)), (209/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1124283958075/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111147859991439/39614081257132168796771975168), (-1329958328129/633825300114114700748351602688)), (23083/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889288548886975/39614081257132168796771975168), (-93493707123/2475880078570760549798248448)), (51941/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889035399630373/2475880078570760549798248448), (-198626801275/309485009821345068724781056)), (6899/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770701771434897/154742504910672534362390528), (-1588588647115/154742504910672534362390528)), (110395/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774547598283763/4835703278458516698824704), (-1488849637611/9671406556917033397649408)), (103507/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629193931634945/302231454903657293676544), (-1302291387387/604462909807314587353088)), (22645/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887140955285035/75557863725914323419136), (-2115376287751/75557863725914323419136)), (73607/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648525674269319/2361183241434822606848), (-396447817395/1180591620717411303424)), (55215/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620777315215791/590295810358705651712), (-1089629824231/295147905179352825856)), (2373/9223372036854775808), by norm_num⟩
  | 8 => ⟨((227829579376353/9223372036854775808), (-2722270747233/73786976294838206464)), (189887/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113857178587889/576460752303423488), (-382509538501/1152921504606846976)), (213687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398241056556075/288230376151711744), (-3056981393313/1152921504606846976)), (26721/144115188075855872), by norm_num⟩
  | 5 => ⟨((596843901145913/72057594037927936), (-2671380976641/144115188075855872)), (93569/72057594037927936), by norm_num⟩
  | 4 => ⟨((186287487271413/4503599627370496), (-250007878697/2251799813685248)), (35111/4503599627370496), by norm_num⟩
  | 3 => ⟨((185948648538651/1125899906842624), (-4988025758739/9007199254740992)), (175715/4503599627370496), by norm_num⟩
  | 2 => ⟨((34759706895427/70368744177664), (-4969873242867/2251799813685248)), (703819/4503599627370496), by norm_num⟩
  | 1 => ⟨((8637260871273/8796093022208), (-14819172851985/2251799813685248)), (1058139/2251799813685248), by norm_num⟩
  | 0 => ⟨((542725998473191/562949953421312), (-7319611615191/562949953421312)), (2125973/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542725998473191/562949953421312), (-7319611615191/562949953421312)), (8109943398482512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1046266833897835/1125899906842624), (-56453238845087/2251799813685248)), (4154481/2251799813685248), by norm_num⟩
  | 2 => ⟨((1943116859718285/2251799813685248), (-52460392891731/1125899906842624)), (7929591/2251799813685248), by norm_num⟩
  | 3 => ⟨((208982540119253/281474976710656), (-90537953929875/1125899906842624)), (3606027/562949953421312), by norm_num⟩
  | 4 => ⟨((613360128992215/1125899906842624), (-268881473025789/2251799813685248)), (370911/35184372088832), by norm_num⟩
  | 5 => ⟨((159044482563083/562949953421312), (-585917714270731/4503599627370496)), (63066085/4503599627370496), by norm_num⟩
  | 6 => ⟨((283237848256307/4503599627370496), (-662133314866741/9007199254740992)), (104089219/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1293933111/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile000Terms1

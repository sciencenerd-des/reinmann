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
namespace Reinmann.XiBand97.Tile049Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨49,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15131/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15131/512))
  have he : value ((69/80), (15131/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-17022057/262144)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-685963078803279/9007199254740992), (-1167149669513219/9007199254740992)), (60460515/4503599627370496), by norm_num⟩
  | 1 => ⟨((2874784347/17179869184), (1222844095/4294967296)), (255/8589934592), by norm_num⟩
  | 2 => ⟨((-3158273411/17179869184), (-671715775/2147483648)), (563/17179869184), by norm_num⟩
  | 3 => ⟨((289143165/2147483648), (3935761093/17179869184)), (207/8589934592), by norm_num⟩
  | 4 => ⟨((-1270624937/17179869184), (-2161937751/17179869184)), (457/34359738368), by norm_num⟩
  | 5 => ⟨((139592417/4294967296), (3800210209/68719476736)), (101/17179869184), by norm_num⟩
  | 6 => ⟨((-1635818077/137438953472), (-1391652545/68719476736)), (149/68719476736), by norm_num⟩
  | 7 => ⟨((513465669/137438953472), (1747298957/274877906944)), (47/68719476736), by norm_num⟩
  | 8 => ⟨((-2256398775/2199023255552), (-959802053/549755813888)), (415/2199023255552), by norm_num⟩
  | 9 => ⟨((137717079/549755813888), (3749156729/8796093022208)), (51/1099511627776), by norm_num⟩
  | 10 => ⟨((-1936610245/35184372088832), (-823773931/8796093022208)), (361/35184372088832), by norm_num⟩
  | 11 => ⟨((3094667365/281474976710656), (5265502043/281474976710656)), (145/70368744177664), by norm_num⟩
  | 12 => ⟨((-2266559731/1125899906842624), (-1928248417/562949953421312)), (427/1125899906842624), by norm_num⟩
  | 13 => ⟨((1532350999/4503599627370496), (5214516693/9007199254740992)), (145/2251799813685248), by norm_num⟩
  | 14 => ⟨((-120247117/2251799813685248), (-3273561211/36028797018963968)), (183/18014398509481984), by norm_num⟩
  | 15 => ⟨((563647831/72057594037927936), (3836132879/288230376151711744)), (431/288230376151711744), by norm_num⟩
  | 16 => ⟨((-2476921735/2305843009213693952), (-2107211361/1152921504606846976)), (119/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1369136823091/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779040237706637/633825300114114700748351602688), (-1620782282739/316912650057057350374175801344)), (11565/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890046928254261/39614081257132168796771975168), (-3646143270653/39614081257132168796771975168)), (52053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118115041173321/154742504910672534362390528), (-1936638539839/1237940039285380274899124224)), (27659/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885753223552421/77371252455336267181195264), (-3872433280589/154742504910672534362390528)), (55331/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193731120045501/1208925819614629174706176), (-907377454629/2417851639229258349412352)), (51887/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629523393640215/302231454903657293676544), (-3174924882817/604462909807314587353088)), (45415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888210546300041/75557863725914323419136), (-5157572912923/75557863725914323419136)), (73827/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81115782941683/295147905179352825856), (-3866710034869/4722366482869645213696)), (55393/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810938644037461/295147905179352825856), (-1328584702305/147573952589676412928)), (19051/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824009131974097/73786976294838206464), (-1659835872527/18446744073709551616)), (95311/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455813881305623/2305843009213693952), (-7464340866359/9223372036854775808)), (107303/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797250330295671/576460752303423488), (-7458193121325/1152921504606846976)), (107401/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597513713736717/72057594037927936), (-6519006832437/144115188075855872)), (47043/72057594037927936), by norm_num⟩
  | 4 => ⟨((746149922747305/18014398509481984), (-4882348058151/18014398509481984)), (35337/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490072557609269/9007199254740992), (-6090859148071/4503599627370496)), (11067/562949953421312), by norm_num⟩
  | 2 => ⟨((557384614692417/1125899906842624), (-12145536314167/2251799813685248)), (44413/562949953421312), by norm_num⟩
  | 1 => ⟨((1109195706008957/1125899906842624), (-2266001238603/140737488355328)), (267929/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092460042899291/1125899906842624), (-35895804879899/1125899906842624)), (270843/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092460042899291/1125899906842624), (-35895804879899/1125899906842624)), (1033184053661155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((132358617013611/140737488355328), (-34829679175451/562949953421312)), (1085737/1125899906842624), by norm_num⟩
  | 2 => ⟨((1983037729847775/2251799813685248), (-65512156292733/562949953421312)), (68017/35184372088832), by norm_num⟩
  | 3 => ⟨((1715858191551441/2251799813685248), (-230771984086029/1125899906842624)), (2170055/562949953421312), by norm_num⟩
  | 4 => ⟨((1212872690707099/2251799813685248), (-175846892280603/562949953421312)), (8393433/1125899906842624), by norm_num⟩
  | 5 => ⟨((216783500365723/1125899906842624), (-757722394669913/2251799813685248)), (1785683/140737488355328), by norm_num⟩
  | 6 => ⟨((-685963078803279/9007199254740992), (-1167149669513219/9007199254740992)), (60460515/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-17022057/262144)), (1/33554432), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-66638419/33554432), (-35676585/524288)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((18637486295369/281474976710656), (135352851776707/1125899906842624)), (40836185/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1309643497/8589934592), (-2377788229/8589934592)), (361/17179869184), by norm_num⟩
  | 2 => ⟨((3015565593/17179869184), (2737529865/8589934592)), (209/8589934592), by norm_num⟩
  | 3 => ⟨((-2314532127/17179869184), (-4202263639/17179869184)), (323/17179869184), by norm_num⟩
  | 4 => ⟨((1332351793/17179869184), (2419017403/17179869184)), (187/17179869184), by norm_num⟩
  | 5 => ⟨((-1227141351/34359738368), (-4455994729/68719476736)), (347/68719476736), by norm_num⟩
  | 6 => ⟨((470932897/34359738368), (1710051173/68719476736)), (269/137438953472), by norm_num⟩
  | 7 => ⟨((-619636039/137438953472), (-562505477/68719476736)), (89/137438953472), by norm_num⟩
  | 8 => ⟨((2853529413/2199023255552), (647608363/274877906944)), (103/549755813888), by norm_num⟩
  | 9 => ⟨((-730054921/2199023255552), (-2650974867/4398046511104)), (53/1099511627776), by norm_num⟩
  | 10 => ⟨((2689621725/35184372088832), (610409521/4398046511104)), (393/35184372088832), by norm_num⟩
  | 11 => ⟨((-1126015071/70368744177664), (-2044392529/70368744177664)), (83/35184372088832), by norm_num⟩
  | 12 => ⟨((1728497011/562949953421312), (3138258507/562949953421312)), (257/562949953421312), by norm_num⟩
  | 13 => ⟨((-306154727/562949953421312), (-2223417617/2251799813685248)), (367/4503599627370496), by norm_num⟩
  | 14 => ⟨((805654069/9007199254740992), (1462745217/9007199254740992)), (243/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1978759519/144115188075855872), (-898158755/36028797018963968)), (75/36028797018963968), by norm_num⟩
  | 16 => ⟨((2278131085/1152921504606846976), (4136173921/1152921504606846976)), (87/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (86896633437/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444726072688487/158456325028528675187087900672), (1645643068261/633825300114114700748351602688)), (23091/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889894252676673/39614081257132168796771975168), (462756392435/9903520314283042199192993792)), (6495/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889678780976559/2475880078570760549798248448), (983158076011/1237940039285380274899124224)), (55213/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110709059472847/9671406556917033397649408), (982933979789/77371252455336267181195264)), (13805/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774848982111339/4835703278458516698824704), (1842525138459/9671406556917033397649408)), (51775/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629457535667125/302231454903657293676544), (1611733569685/604462909807314587353088)), (45311/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887997268003301/75557863725914323419136), (1309087500635/37778931862957161709568)), (18411/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648846616458235/2361183241434822606848), (981425510105/2361183241434822606848)), (55245/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621659337555921/590295810358705651712), (2697652863613/590295810358705651712)), (18995/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113983644406101/4611686018427387904), (3370166170389/73786976294838206464)), (23751/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455738267792291/2305843009213693952), (3788826230781/9223372036854775808)), (106919/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594200977451143/1152921504606846976), (3785565336797/1152921504606846976)), (106969/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194768316204097/144115188075855872), (206794036973/9007199254740992)), (46827/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491917387066877/36028797018963968), (1238933823121/9007199254740992)), (140593/36028797018963968), by norm_num⟩
  | 3 => ⟨((744802658436855/4503599627370496), (6181875566787/9007199254740992)), (175937/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228636344290961/4503599627370496), (3081361837845/1125899906842624)), (352463/4503599627370496), by norm_num⟩
  | 1 => ⟨((69284959504987/70368744177664), (9196340063267/1125899906842624)), (530173/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182693812153503/2251799813685248), (18202502112969/1125899906842624)), (533143/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182693812153503/2251799813685248), (18202502112969/1125899906842624)), (2033779148582076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115120058334919/2251799813685248), (4410970336509/140737488355328)), (2101603/2251799813685248), by norm_num⟩
  | 2 => ⟨((992262262664015/1125899906842624), (66291731822833/1125899906842624)), (4079817/2251799813685248), by norm_num⟩
  | 3 => ⟨((870583431299679/1125899906842624), (233693185032423/2251799813685248)), (7671565/2251799813685248), by norm_num⟩
  | 4 => ⟨((661037788659223/1125899906842624), (22587422476503/140737488355328)), (13456141/2251799813685248), by norm_num⟩
  | 5 => ⟨((359107137067683/1125899906842624), (212184258506613/1125899906842624)), (20119967/2251799813685248), by norm_num⟩
  | 6 => ⟨((18637486295369/281474976710656), (135352851776707/1125899906842624)), (40836185/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-35676585/524288)), (1/33554432), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-1188906709/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-202201289414595/9007199254740992), (-1120548294372069/9007199254740992)), (24002187/2251799813685248), by norm_num⟩
  | 1 => ⟨((1806235/33554432), (2562482317/8589934592)), (441/17179869184), by norm_num⟩
  | 2 => ⟨((-554388783/8589934592), (-6144564235/17179869184)), (531/17179869184), by norm_num⟩
  | 3 => ⟨((886244161/17179869184), (4911340511/17179869184)), (427/17179869184), by norm_num⟩
  | 4 => ⟨((-531280171/17179869184), (-5888440097/34359738368)), (257/17179869184), by norm_num⟩
  | 5 => ⟨((127395421/8589934592), (5647945069/68719476736)), (495/68719476736), by norm_num⟩
  | 6 => ⟨((-407307837/68719476736), (-2257196797/68719476736)), (397/137438953472), by norm_num⟩
  | 7 => ⟨((1116207471/549755813888), (6185738891/549755813888)), (273/274877906944), by norm_num⟩
  | 8 => ⟨((-669137155/1099511627776), (-3708188511/1099511627776)), (165/549755813888), by norm_num⟩
  | 9 => ⟨((713120365/4398046511104), (493991539/549755813888)), (177/2199023255552), by norm_num⟩
  | 10 => ⟨((-683995181/17592186044416), (-947631981/4398046511104)), (341/17592186044416), by norm_num⟩
  | 11 => ⟨((1192835499/140737488355328), (6610391993/140737488355328)), (597/140737488355328), by norm_num⟩
  | 12 => ⟨((-953431535/562949953421312), (-20639359/2199023255552)), (479/562949953421312), by norm_num⟩
  | 13 => ⟨((175863767/562949953421312), (974592421/562949953421312)), (355/2251799813685248), by norm_num⟩
  | 14 => ⟨((-963892333/18014398509481984), (-5341646993/18014398509481984)), (489/18014398509481984), by norm_num⟩
  | 15 => ⟨((1232700197/144115188075855872), (6831312039/144115188075855872)), (157/36028797018963968), by norm_num⟩
  | 16 => ⟨((-369485747/288230376151711744), (-4095192711/576460752303423488)), (189/288230376151711744), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-284836176109/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111173444513557/39614081257132168796771975168), (-168546192637/39614081257132168796771975168)), (46233/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944874407247191/19807040628566084398385987584), (-1516638708203/19807040628566084398385987584)), (52021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889524104704615/2475880078570760549798248448), (-1611088367409/1237940039285380274899124224)), (27641/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771190108719977/154742504910672534362390528), (-201338208473/9671406556917033397649408)), (55293/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549552622198137/9671406556917033397649408), (-1509630043477/4835703278458516698824704)), (51849/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314696930087405/151115727451828646838272), (-1320519878493/302231454903657293676544)), (11345/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943894995810605/37778931862957161709568), (-4290166038927/75557863725914323419136)), (18441/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297537486281753/4722366482869645213696), (-3216291878347/4722366482869645213696)), (55343/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810722358156871/295147905179352825856), (-2210118327665/295147905179352825856)), (76127/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911734665257341/36893488147419103232), (-2761025171557/36893488147419103232)), (47603/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911324751546799/4611686018427387904), (-6207846608341/9223372036854775808)), (26793/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796948102406055/576460752303423488), (-6202275325435/1152921504606846976)), (107253/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597250144173969/72057594037927936), (-5420728373113/144115188075855872)), (93939/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491512650017855/36028797018963968), (-4059290186091/18014398509481984)), (141091/36028797018963968), by norm_num⟩
  | 3 => ⟨((372273674388523/2251799813685248), (-5063179057133/4503599627370496)), (176685/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227601086268375/4503599627370496), (-20187230004615/4503599627370496)), (354335/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215531029111407/2251799813685248), (-15058767244781/1125899906842624)), (533923/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179380866262851/2251799813685248), (-59584254285841/2251799813685248)), (134695/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179380866262851/2251799813685248), (-59584254285841/2251799813685248)), (513820649267101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((263464287990279/281474976710656), (-115335992952749/2251799813685248)), (1071419/1125899906842624), by norm_num⟩
  | 2 => ⟨((1966940919334795/2251799813685248), (-215912019022453/2251799813685248)), (264435/140737488355328), by norm_num⟩
  | 3 => ⟨((1697414910937337/2251799813685248), (-188598552415911/1125899906842624)), (8202829/2251799813685248), by norm_num⟩
  | 4 => ⟨((608166788924369/1125899906842624), (-568665106207725/2251799813685248)), (1889343/281474976710656), by norm_num⟩
  | 5 => ⟨((256702963238113/1125899906842624), (-614340989840811/2251799813685248)), (5990719/562949953421312), by norm_num⟩
  | 6 => ⟨((-202201289414595/9007199254740992), (-1120548294372069/9007199254740992)), (24002187/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1188906709/16777216)), (1/33554432), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-17978733/8388608), (-2464096093/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-201601974483585/4503599627370496), (976340508118145/9007199254740992)), (46488561/4503599627370496), by norm_num⟩
  | 1 => ⟨((1911018703/17179869184), (-36151931/134217728)), (443/17179869184), by norm_num⟩
  | 2 => ⟨((-2374351541/17179869184), (5749387119/17179869184)), (553/17179869184), by norm_num⟩
  | 3 => ⟨((491670161/4294967296), (-4762230095/17179869184)), (461/17179869184), by norm_num⟩
  | 4 => ⟨((-2443508905/34359738368), (5916848615/34359738368)), (575/34359738368), by norm_num⟩
  | 5 => ⟨((2428756611/68719476736), (-5881126587/68719476736)), (287/34359738368), by norm_num⟩
  | 6 => ⟨((-502936121/34359738368), (1217837547/34359738368)), (239/68719476736), by norm_num⟩
  | 7 => ⟨((1428284927/274877906944), (-3458528707/274877906944)), (341/274877906944), by norm_num⟩
  | 8 => ⟨((-443644339/274877906944), (4297060491/1099511627776)), (213/549755813888), by norm_num⟩
  | 9 => ⟨((1959848477/4398046511104), (-2372843153/2199023255552)), (473/4398046511104), by norm_num⟩
  | 10 => ⟨((-1948016205/17592186044416), (589629373/2199023255552)), (59/2199023255552), by norm_num⟩
  | 11 => ⟨((1760232153/70368744177664), (-2131162109/35184372088832)), (429/70368744177664), by norm_num⟩
  | 12 => ⟨((-729002097/140737488355328), (3530492597/281474976710656)), (357/281474976710656), by norm_num⟩
  | 13 => ⟨((1114770559/1125899906842624), (-674841887/281474976710656)), (137/562949953421312), by norm_num⟩
  | 14 => ⟨((-1582914729/9007199254740992), (1916478963/4503599627370496)), (391/9007199254740992), by norm_num⟩
  | 15 => ⟨((1048905423/36028797018963968), (-2539878037/36028797018963968)), (65/9007199254740992), by norm_num⟩
  | 16 => ⟨((-651608015/144115188075855872), (394459989/36028797018963968)), (325/288230376151711744), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (1278146993955/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889329210487681/316912650057057350374175801344), (1512449232035/316912650057057350374175801344)), (23125/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944808752509397/19807040628566084398385987584), (3402366187711/39614081257132168796771975168)), (52041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944692272130929/1237940039285380274899124224), (3614222896435/2475880078570760549798248448)), (6913/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885525249352525/77371252455336267181195264), (1806666512179/77371252455336267181195264)), (13829/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549421685193177/9671406556917033397649408), (1693277222787/4835703278458516698824704)), (1621/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629336548957797/302231454903657293676544), (1481145063663/302231454903657293676544)), (22701/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235950453969503/9444732965739290427392), (4811950094265/75557863725914323419136)), (36901/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297397630404257/4722366482869645213696), (1803706582111/2361183241434822606848)), (55373/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202656534376325/73786976294838206464), (4957676319837/590295810358705651712)), (76173/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455807142526095/18446744073709551616), (3096660993029/36893488147419103232)), (47635/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822378361249145/9223372036854775808), (6962301646221/9223372036854775808)), (107251/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796812353012551/576460752303423488), (6955823943935/1152921504606846976)), (107343/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194262326771403/144115188075855872), (759883052921/18014398509481984)), (23507/36028797018963968), by norm_num⟩
  | 4 => ⟨((745577455463627/18014398509481984), (9104048294423/36028797018963968)), (141247/36028797018963968), by norm_num⟩
  | 3 => ⟨((744323068695619/4503599627370496), (2838658466993/2251799813685248)), (176919/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113349919420661/2251799813685248), (22633120561491/4503599627370496)), (177461/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214168951127845/2251799813685248), (8439943945403/562949953421312)), (535099/2251799813685248), by norm_num⟩
  | 0 => ⟨((544154136336425/562949953421312), (16690676610733/562949953421312)), (1081101/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544154136336425/562949953421312), (16690676610733/562949953421312)), (4124073037154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((131372755077271/140737488355328), (2016675874291/35184372088832)), (1077059/1125899906842624), by norm_num⟩
  | 2 => ⟨((1954700686756209/2251799813685248), (240958129964813/2251799813685248)), (2134251/1125899906842624), by norm_num⟩
  | 3 => ⟨((835508097021055/1125899906842624), (209166471752603/1125899906842624)), (2081041/562949953421312), by norm_num⟩
  | 4 => ⟨((1162311433379969/2251799813685248), (620873240019029/2251799813685248)), (3861819/562949953421312), by norm_num⟩
  | 5 => ⟨((857522309155875/4503599627370496), (1281904476886423/4503599627370496)), (12232591/1125899906842624), by norm_num⟩
  | 6 => ⟨((-201601974483585/4503599627370496), (976340508118145/9007199254740992)), (46488561/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-2464096093/33554432)), (1/33554432), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-148462847/67108864), (-5086936921/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((906861236045501/9007199254740992), (-386672228351449/9007199254740992)), (21673917/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4436594285/17179869184), (945849117/8589934592)), (107/8589934592), by norm_num⟩
  | 2 => ⟨((2844909915/8589934592), (-2426055085/17179869184)), (277/17179869184), by norm_num⟩
  | 3 => ⟨((-2432349953/8589934592), (129639759/1073741824)), (239/17179869184), by norm_num⟩
  | 4 => ⟨((389928403/2147483648), (-665038833/8589934592)), (155/17179869184), by norm_num⟩
  | 5 => ⟨((-3200469141/34359738368), (682316371/17179869184)), (161/34359738368), by norm_num⟩
  | 6 => ⟨((2736347089/68719476736), (-583368979/34359738368)), (139/68719476736), by norm_num⟩
  | 7 => ⟨((-4010623833/274877906944), (1710070729/274877906944)), (205/274877906944), by norm_num⟩
  | 8 => ⟨((642940439/137438953472), (-2193122409/1099511627776)), (265/1099511627776), by norm_num⟩
  | 9 => ⟨((-2931750517/2199023255552), (312513773/549755813888)), (19/274877906944), by norm_num⟩
  | 10 => ⟨((1503958321/4398046511104), (-641265601/4398046511104)), (157/8796093022208), by norm_num⟩
  | 11 => ⟨((-1402755247/17592186044416), (299057053/8796093022208)), (37/8796093022208), by norm_num⟩
  | 12 => ⟨((2398664113/140737488355328), (-63922183/8796093022208)), (255/281474976710656), by norm_num⟩
  | 13 => ⟨((-946531073/281474976710656), (1614347443/1125899906842624)), (51/281474976710656), by norm_num⟩
  | 14 => ⟨((5549266897/9007199254740992), (-147882837/562949953421312)), (301/9007199254740992), by norm_num⟩
  | 15 => ⟨((-59306619/562949953421312), (809198907/18014398509481984)), (13/2251799813685248), by norm_num⟩
  | 16 => ⟨((4867791177/288230376151711744), (-2075554217/288230376151711744)), (269/288230376151711744), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039973471/10141204801825835211973625643008), (-525008971997/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778556706119809/633825300114114700748351602688), (-310589837889/316912650057057350374175801344)), (46131/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944751681171375/19807040628566084398385987584), (-174673156327/9903520314283042199192993792)), (12975/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472315910148991/618970019642690137449562112), (-742193439025/2475880078570760549798248448)), (27573/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770930014241149/154742504910672534362390528), (-185501276321/38685626227668133590597632)), (13787/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549309176128857/9671406556917033397649408), (-347714874263/4835703278458516698824704)), (6463/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258575097288101/604462909807314587353088), (-76037633449/75557863725914323419136)), (11311/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887445214070621/75557863725914323419136), (-988114465359/75557863725914323419136)), (36763/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648639772817643/2361183241434822606848), (-92594760701/590295810358705651712)), (55149/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101318193187369/36893488147419103232), (-1018010051779/590295810358705651712)), (75837/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823028861702487/73786976294838206464), (-158964326851/9223372036854775808)), (94807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822156121689739/9223372036854775808), (-1429582611363/9223372036854775808)), (106673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593405501597717/1152921504606846976), (-1428213473649/1152921504606846976)), (106693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298518482515503/36028797018963968), (-1248148261059/144115188075855872)), (46689/72057594037927936), by norm_num⟩
  | 4 => ⟨((745439555911719/18014398509481984), (-1869149708313/36028797018963968)), (140109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488313240190297/9007199254740992), (-582767441315/2251799813685248)), (175211/9007199254740992), by norm_num⟩
  | 2 => ⟨((139129339678775/281474976710656), (-1161519162215/1125899906842624)), (43831/562949953421312), by norm_num⟩
  | 1 => ⟨((1106655623405681/1125899906842624), (-3464547369427/1125899906842624)), (32909/140737488355328), by norm_num⟩
  | 0 => ⟨((2175249310973031/2251799813685248), (-1712365964677/281474976710656)), (527699/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175249310973031/2251799813685248), (-1712365964677/281474976710656)), (2013011936668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2101217823854657/2251799813685248), (-26466458427857/2251799813685248)), (2051881/2251799813685248), by norm_num⟩
  | 2 => ⟨((980197227798471/1125899906842624), (-12348298868519/562949953421312)), (1938785/1125899906842624), by norm_num⟩
  | 3 => ⟨((1705616418668439/2251799813685248), (-86002446543527/2251799813685248)), (6921657/2251799813685248), by norm_num⟩
  | 4 => ⟨((644313701685357/1125899906842624), (-65142196024179/1125899906842624)), (2753569/562949953421312), by norm_num⟩
  | 5 => ⟨((91237382199657/281474976710656), (-74557266060985/1125899906842624)), (13880707/2251799813685248), by norm_num⟩
  | 6 => ⟨((906861236045501/9007199254740992), (-386672228351449/9007199254740992)), (21673917/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148462847/67108864), (-5086936921/67108864)), (1/33554432), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2386755/1048576), (-5233911589/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-789171888537611/9007199254740992), (-482170561350021/9007199254740992)), (83704921/9007199254740992), by norm_num⟩
  | 1 => ⟨((124136797/536870912), (1213527445/8589934592)), (53/2147483648), by norm_num⟩
  | 2 => ⟨((-81901031/268435456), (-1601284249/8589934592)), (281/8589934592), by norm_num⟩
  | 3 => ⟨((4611019011/17179869184), (704313489/4294967296)), (31/1073741824), by norm_num⟩
  | 4 => ⟨((-3042185879/17179869184), (-1858723675/17179869184)), (329/17179869184), by norm_num⟩
  | 5 => ⟨((3211401177/34359738368), (1962111335/34359738368)), (349/34359738368), by norm_num⟩
  | 6 => ⟨((-1412511969/34359738368), (-1726041433/68719476736)), (309/68719476736), by norm_num⟩
  | 7 => ⟨((4260228645/274877906944), (2602927025/274877906944)), (117/68719476736), by norm_num⟩
  | 8 => ⟨((-702686727/137438953472), (-1717318411/549755813888)), (311/549755813888), by norm_num⟩
  | 9 => ⟨((3296765435/2199023255552), (125891715/137438953472)), (367/2199023255552), by norm_num⟩
  | 10 => ⟨((-1740070597/4398046511104), (-531576725/2199023255552)), (389/8796093022208), by norm_num⟩
  | 11 => ⟨((3339742591/35184372088832), (2040525749/35184372088832)), (375/35184372088832), by norm_num⟩
  | 12 => ⟨((-1468962027/70368744177664), (-897510739/70368744177664)), (83/35184372088832), by norm_num⟩
  | 13 => ⟨((4771292313/1125899906842624), (91099319/35184372088832)), (271/562949953421312), by norm_num⟩
  | 14 => ⟨((-3597632557/4503599627370496), (-2198092119/4503599627370496)), (205/2251799813685248), by norm_num⟩
  | 15 => ⟨((5063657903/36028797018963968), (773452149/9007199254740992)), (579/36028797018963968), by norm_num⟩
  | 16 => ⟨((-835205219/36028797018963968), (-2041184563/144115188075855872)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-422231239411/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889224925969809/316912650057057350374175801344), (-1998089971311/316912650057057350374175801344)), (46297/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889382706996829/39614081257132168796771975168), (-280924518239/2475880078570760549798248448)), (52097/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889134858475191/2475880078570760549798248448), (-4774605874829/2475880078570760549798248448)), (6921/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770800573681413/154742504910672534362390528), (-2386678126335/77371252455336267181195264)), (6923/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549187126513665/9671406556917033397649408), (-1118423507087/2417851639229258349412352)), (51941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258467605347955/604462909807314587353088), (-3913155113977/604462909807314587353088)), (45465/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471817307781751/18889465931478580854784), (-6207411393/73786976294838206464)), (36957/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297146414650535/4722366482869645213696), (-4765115763201/4722366482869645213696)), (6933/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620906179497553/590295810358705651712), (-6548499058245/590295810358705651712)), (38155/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911397470825915/36893488147419103232), (-8180323226707/73786976294838206464)), (95457/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821889144567257/9223372036854775808), (-2298894672173/2305843009213693952)), (53743/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796566881338749/576460752303423488), (-4593238790853/576460752303423488)), (53803/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193830814577121/144115188075855872), (-1003492014147/18014398509481984)), (23573/36028797018963968), by norm_num⟩
  | 4 => ⟨((745251891709301/18014398509481984), (-6010729037761/18014398509481984)), (141709/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487825506520551/9007199254740992), (-14991081216267/9007199254740992)), (88807/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112519270465675/2251799813685248), (-14937547797503/2251799813685248)), (89165/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105813680757641/1125899906842624), (-2784095469101/140737488355328)), (269291/1125899906842624), by norm_num⟩
  | 0 => ⟨((542834367640651/562949953421312), (-44012951994417/1125899906842624)), (545795/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((542834367640651/562949953421312), (-44012951994417/1125899906842624)), (2082042698386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045154596489829/1125899906842624), (-84880522038189/1125899906842624)), (547629/562949953421312), by norm_num⟩
  | 2 => ⟨((1927601949245069/2251799813685248), (-157586419932211/1125899906842624)), (4397123/2251799813685248), by norm_num⟩
  | 3 => ⟨((1605966628901527/2251799813685248), (-67449132997917/281474976710656)), (1094875/281474976710656), by norm_num⟩
  | 4 => ⟨((1016061962764785/2251799813685248), (-769667399985931/2251799813685248)), (4172875/562949953421312), by norm_num⟩
  | 5 => ⟨((97698295137577/1125899906842624), (-173645491120705/562949953421312)), (6618373/562949953421312), by norm_num⟩
  | 6 => ⟨((-789171888537611/9007199254740992), (-482170561350021/9007199254740992)), (83704921/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-5233911589/67108864)), (1/33554432), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-5370741731/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-139836789639375/18014398509481984), (1737154753568867/18014398509481984)), (17996929/2251799813685248), by norm_num⟩
  | 1 => ⟨((361142203/17179869184), (-4486372261/17179869184)), (187/8589934592), by norm_num⟩
  | 2 => ⟨((-61124451/2147483648), (1518665163/4294967296)), (127/4294967296), by norm_num⟩
  | 3 => ⟨((220704109/8589934592), (-2741747667/8589934592)), (461/17179869184), by norm_num⟩
  | 4 => ⟨((-597677807/34359738368), (7424790321/34359738368)), (627/34359738368), by norm_num⟩
  | 5 => ⟨((323708301/34359738368), (-4021340985/34359738368)), (341/34359738368), by norm_num⟩
  | 6 => ⟨((-146103055/34359738368), (7259995509/137438953472)), (309/68719476736), by norm_num⟩
  | 7 => ⟨((226088233/137438953472), (-5617266371/274877906944)), (15/8589934592), by norm_num⟩
  | 8 => ⟨((-612258285/1099511627776), (7605919663/1099511627776)), (163/274877906944), by norm_num⟩
  | 9 => ⟨((92112565/549755813888), (-4577158283/2199023255552)), (197/1099511627776), by norm_num⟩
  | 10 => ⟨((-24944545/549755813888), (1239517441/2199023255552)), (429/8796093022208), by norm_num⟩
  | 11 => ⟨((196512233/17592186044416), (-2441218513/17592186044416)), (53/4398046511104), by norm_num⟩
  | 12 => ⟨((-354776661/140737488355328), (4407294857/140737488355328)), (385/140737488355328), by norm_num⟩
  | 13 => ⟨((147808155/281474976710656), (-7344723523/1125899906842624)), (161/281474976710656), by norm_num⟩
  | 14 => ⟨((-114363401/1125899906842624), (5682822861/4503599627370496)), (125/1125899906842624), by norm_num⟩
  | 15 => ⟨((82587155/4503599627370496), (-4103831891/18014398509481984)), (363/18014398509481984), by norm_num⟩
  | 16 => ⟨((-447300323/144115188075855872), (5556691389/144115188075855872)), (493/144115188075855872), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (2150769098343/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778363239540667/633825300114114700748351602688), (2544226708633/633825300114114700748351602688)), (23113/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889285573250367/39614081257132168796771975168), (715417450083/9903520314283042199192993792)), (13003/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236129006630843/309485009821345068724781056), (3039799404643/2475880078570760549798248448)), (6909/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770698216961195/154742504910672534362390528), (759746079533/38685626227668133590597632)), (55283/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549091643523411/9671406556917033397649408), (2848182027183/9671406556917033397649408)), (51839/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258384533809321/604462909807314587353088), (2491293793303/604462909807314587353088)), (22685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887135131764163/75557863725914323419136), (505841281941/9444732965739290427392)), (73747/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40532706867869/147573952589676412928), (3033628919995/4722366482869645213696)), (55329/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405192556759811/147573952589676412928), (1042233854431/147573952589676412928)), (38053/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455656724211133/18446744073709551616), (650964346821/9223372036854775808)), (47589/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821702696802917/9223372036854775808), (5853932473503/9223372036854775808)), (837/72057594037927936), by norm_num⟩
  | 6 => ⟨((199118820271611/144115188075855872), (5848004090307/1152921504606846976)), (107213/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193674158999885/144115188075855872), (638792614695/18014398509481984)), (46949/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490276069051465/36028797018963968), (956525370493/4503599627370496)), (35255/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487553537742395/9007199254740992), (4771000997303/4503599627370496)), (176579/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224532440025515/4503599627370496), (4753600179307/1125899906842624)), (354071/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105481076426739/1125899906842624), (7087030890827/562949953421312)), (533395/2251799813685248), by norm_num⟩
  | 0 => ⟨((542594735995865/562949953421312), (28002757185463/1125899906842624)), (268997/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542594735995865/562949953421312), (28002757185463/1125899906842624)), (1026142122508811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2090509162598589/2251799813685248), (107960919437763/2251799813685248)), (2127689/2251799813685248), by norm_num⟩
  | 2 => ⟨((1935595239103275/2251799813685248), (50113977698099/562949953421312)), (2077299/1125899906842624), by norm_num⟩
  | 3 => ⟨((1645948425318469/2251799813685248), (344614564955379/2251799813685248)), (7882081/2251799813685248), by norm_num⟩
  | 4 => ⟨((287590731277039/562949953421312), (503790609700619/2251799813685248)), (3483831/562949953421312), by norm_num⟩
  | 5 => ⟨((59370834972809/281474976710656), (514736732719379/2251799813685248)), (5118387/562949953421312), by norm_num⟩
  | 6 => ⟨((-139836789639375/18014398509481984), (1737154753568867/18014398509481984)), (17996929/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-5370741731/67108864)), (1/33554432), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile049Terms1

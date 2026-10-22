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
namespace Reinmann.XiBand97.Tile034Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32547/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32547/1280))
  have he : value ((69/80), (32547/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1182786455/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((305274648535797/18014398509481984), (-1619899965873299/18014398509481984)), (250585791/9007199254740992), by norm_num⟩
  | 1 => ⟨((-201797735/4294967296), (1070813269/4294967296)), (333/4294967296), by norm_num⟩
  | 2 => ⟨((139875531/2147483648), (-1484462397/4294967296)), (29/268435456), by norm_num⟩
  | 3 => ⟨((-16159055/268435456), (1371934567/4294967296)), (431/4294967296), by norm_num⟩
  | 4 => ⟨((179209655/4294967296), (-950952577/4294967296)), (75/1073741824), by norm_num⟩
  | 5 => ⟨((-198749867/8589934592), (263660039/2147483648)), (335/8589934592), by norm_num⟩
  | 6 => ⟨((22960485/2147483648), (-243673617/4294967296)), (311/17179869184), by norm_num⟩
  | 7 => ⟨((-72754265/17179869184), (1544243937/68719476736)), (495/68719476736), by norm_num⟩
  | 8 => ⟨((201717655/137438953472), (-1070388331/137438953472)), (345/137438953472), by norm_num⟩
  | 9 => ⟨((-248568931/549755813888), (41218703/17179869184)), (427/549755813888), by norm_num⟩
  | 10 => ⟨((137835883/1099511627776), (-731408071/1099511627776)), (475/2199023255552), by norm_num⟩
  | 11 => ⟨((-69484039/2199023255552), (184353979/1099511627776)), (481/8796093022208), by norm_num⟩
  | 12 => ⟨((256867551/35184372088832), (-1363034035/35184372088832)), (447/35184372088832), by norm_num⟩
  | 13 => ⟨((-27391849/17592186044416), (581405045/70368744177664)), (383/140737488355328), by norm_num⟩
  | 14 => ⟨((173591615/562949953421312), (-921141183/562949953421312)), (305/562949953421312), by norm_num⟩
  | 15 => ⟨((-256692349/4503599627370496), (681052175/2251799813685248)), (453/4503599627370496), by norm_num⟩
  | 16 => ⟨((88962789/9007199254740992), (-472069395/9007199254740992)), (315/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-901751227517/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889139249529753/316912650057057350374175801344), (-2133235689521/633825300114114700748351602688)), (46205/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889190317665379/39614081257132168796771975168), (-1199694946803/19807040628566084398385987584)), (103975/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944465472144095/1237940039285380274899124224), (-2548729797297/2475880078570760549798248448)), (110489/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770597220953899/154742504910672534362390528), (-1274015174589/77371252455336267181195264)), (221013/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387249269873265/2417851639229258349412352), (-597008882595/2417851639229258349412352)), (207237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629150954964273/302231454903657293676544), (-261098554871/75557863725914323419136)), (90685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943500546061167/37778931862957161709568), (-3392889321849/75557863725914323419136)), (73699/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296946286013013/4722366482869645213696), (-2543449663601/4722366482869645213696)), (221159/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810316293127687/295147905179352825856), (-873816552911/147573952589676412928)), (304193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455613830626293/18446744073709551616), (-2183059521531/36893488147419103232)), (380391/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821510330140637/9223372036854775808), (-4907811879355/9223372036854775808)), (214073/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592759012232237/1152921504606846976), (-4902726430377/1152921504606846976)), (428405/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193507469738841/144115188075855872), (-2142085412269/72057594037927936)), (375145/144115188075855872), by norm_num⟩
  | 4 => ⟨((745013932177081/18014398509481984), (-6414842436751/36028797018963968)), (140825/9007199254740992), by norm_num⟩
  | 3 => ⟨((743623236225521/4503599627370496), (-1999653602653/2251799813685248)), (705145/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223927839244013/4503599627370496), (-996097172067/281474976710656)), (1413357/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105039464920389/1125899906842624), (-23757642397101/2251799813685248)), (2127731/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168706336090415/2251799813685248), (-46923490546157/2251799813685248)), (2143189/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168706336090415/2251799813685248), (-46923490546157/2251799813685248)), (8175617222312545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521925320543923/562949953421312), (-90383941450271/2251799813685248)), (8435055/2251799813685248), by norm_num⟩
  | 2 => ⟨((482983362940053/562949953421312), (-167594534209513/2251799813685248)), (8158927/1125899906842624), by norm_num⟩
  | 3 => ⟨((1645030304923455/2251799813685248), (-143787864713265/1125899906842624)), (30428809/2251799813685248), by norm_num⟩
  | 4 => ⟨((582517346350587/1125899906842624), (-420171266550459/2251799813685248)), (52231021/2251799813685248), by norm_num⟩
  | 5 => ⟨((262181818913621/1125899906842624), (-869551723794397/4503599627370496)), (147076889/4503599627370496), by norm_num⟩
  | 6 => ⟨((305274648535797/18014398509481984), (-1619899965873299/18014398509481984)), (250585791/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1182786455/16777216)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1208648921/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1528235322489199/18014398509481984), (-83648930201723/4503599627370496)), (8422921/281474976710656), by norm_num⟩
  | 1 => ⟨((1032308747/4294967296), (113008149/2147483648)), (183/2147483648), by norm_num⟩
  | 2 => ⟨((-1462375459/4294967296), (-80044049/1073741824)), (521/4294967296), by norm_num⟩
  | 3 => ⟨((43158559/134217728), (18898489/268435456)), (247/2147483648), by norm_num⟩
  | 4 => ⟨((-489109621/2147483648), (-214173805/4294967296)), (11/134217728), by norm_num⟩
  | 5 => ⟨((277150381/2147483648), (242720033/8589934592)), (25/536870912), by norm_num⟩
  | 6 => ⟨((-523484105/8589934592), (-229225879/17179869184)), (95/4294967296), by norm_num⟩
  | 7 => ⟨((847509801/34359738368), (371111897/68719476736)), (617/68719476736), by norm_num⟩
  | 8 => ⟨((-1200588039/137438953472), (-262859795/137438953472)), (439/137438953472), by norm_num⟩
  | 9 => ⟨((1511787579/549755813888), (330994613/549755813888)), (555/549755813888), by norm_num⟩
  | 10 => ⟨((-1713286697/2199023255552), (-187555671/1099511627776)), (631/2199023255552), by norm_num⟩
  | 11 => ⟨((220641215/1099511627776), (193230993/4398046511104)), (327/4398046511104), by norm_num⟩
  | 12 => ⟨((-1666996359/35184372088832), (-364976419/35184372088832)), (155/8796093022208), by norm_num⟩
  | 13 => ⟨((363304333/35184372088832), (39771387/17592186044416)), (543/140737488355328), by norm_num⟩
  | 14 => ⟨((-1176364211/562949953421312), (-128778085/281474976710656)), (441/562949953421312), by norm_num⟩
  | 15 => ⟨((888770875/2251799813685248), (97294877/1125899906842624)), (335/2251799813685248), by norm_num⟩
  | 16 => ⟨((-39344961/562949953421312), (-34457143/2251799813685248)), (477/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-3811508403359/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778189484998063/633825300114114700748351602688), (-2253987431747/316912650057057350374175801344)), (185287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944544864197787/19807040628566084398385987584), (-316898047291/2475880078570760549798248448)), (104253/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118051466997873/154742504910672534362390528), (-5385921002863/2475880078570760549798248448)), (55401/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770489078539205/154742504910672534362390528), (-2692203578537/77371252455336267181195264)), (110839/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548894984555439/9671406556917033397649408), (-5046273566835/9671406556917033397649408)), (103951/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629105933026103/302231454903657293676544), (-275867599083/37778931862957161709568)), (181993/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58964169980455/2361183241434822606848), (-1792385934391/18889465931478580854784)), (295887/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162104297843267/590295810358705651712), (-5374521454247/4722366482869645213696)), (111023/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202559603837327/73786976294838206464), (-1846421089503/147573952589676412928)), (76381/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822257799509307/73786976294838206464), (-1153210497635/9223372036854775808)), (382221/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455321058622721/2305843009213693952), (-5185034510471/4611686018427387904)), (430435/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796264037093609/576460752303423488), (-5179521645635/576460752303423488)), (430981/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193299965610959/144115188075855872), (-2262941829703/36028797018963968)), (188861/72057594037927936), by norm_num⟩
  | 4 => ⟨((744852888660841/18014398509481984), (-847055052553/2251799813685248)), (141953/9007199254740992), by norm_num⟩
  | 3 => ⟨((371706247543053/2251799813685248), (-2112225073535/1125899906842624)), (711921/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111514287704809/2251799813685248), (-16832944603351/2251799813685248)), (715159/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104295203355219/1125899906842624), (-12543804556463/562949953421312)), (540429/562949953421312), by norm_num⟩
  | 0 => ⟨((1082588739227427/1125899906842624), (-49529985530621/1125899906842624)), (1097163/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082588739227427/1125899906842624), (-49529985530621/1125899906842624)), (4185344698192405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((129845596367791/140737488355328), (-95249327695419/1125899906842624)), (2206447/562949953421312), by norm_num⟩
  | 2 => ⟨((475157608781113/562949953421312), (-43938917422689/281474976710656)), (8889395/1125899906842624), by norm_num⟩
  | 3 => ⟨((774677173344691/1125899906842624), (-296692959054151/1125899906842624)), (35562981/2251799813685248), by norm_num⟩
  | 4 => ⟨((454834402096271/1125899906842624), (-408280099277899/1125899906842624)), (67681179/2251799813685248), by norm_num⟩
  | 5 => ⟨((17844256678457/562949953421312), (-82467292924657/281474976710656)), (51884371/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1528235322489199/18014398509481984), (-83648930201723/4503599627370496)), (8422921/281474976710656), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1208648921/16777216)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1233032703/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-486713905891965/18014398509481984), (175924649795219/2251799813685248)), (261012825/9007199254740992), by norm_num⟩
  | 1 => ⟨((335403473/4294967296), (-242465801/1073741824)), (361/4294967296), by norm_num⟩
  | 2 => ⟨((-484720363/4294967296), (1401632607/4294967296)), (131/1073741824), by norm_num⟩
  | 3 => ⟨((467007349/4294967296), (-1350413101/4294967296)), (507/4294967296), by norm_num⟩
  | 4 => ⟨((-337456213/4294967296), (243949743/1073741824)), (23/268435456), by norm_num⟩
  | 5 => ⟨((390149563/8589934592), (-282042179/2147483648)), (427/8589934592), by norm_num⟩
  | 6 => ⟨((-187946213/8589934592), (271735583/4294967296)), (413/17179869184), by norm_num⟩
  | 7 => ⟨((38802459/4294967296), (-897619263/34359738368)), (343/34359738368), by norm_num⟩
  | 8 => ⟨((-448614127/137438953472), (324306671/34359738368)), (249/68719476736), by norm_num⟩
  | 9 => ⟨((288147023/274877906944), (-208303743/68719476736)), (161/137438953472), by norm_num⟩
  | 10 => ⟨((-333140807/1099511627776), (481660205/549755813888)), (187/549755813888), by norm_num⟩
  | 11 => ⟨((175072869/2199023255552), (-1012492403/4398046511104)), (395/4398046511104), by norm_num⟩
  | 12 => ⟨((-337350451/17592186044416), (975493149/17592186044416)), (191/8796093022208), by norm_num⟩
  | 13 => ⟨((150010495/35184372088832), (-867550107/70368744177664)), (171/35184372088832), by norm_num⟩
  | 14 => ⟨((-495526969/562949953421312), (716440665/281474976710656)), (567/562949953421312), by norm_num⟩
  | 15 => ⟨((190967621/1125899906842624), (-138051991/281474976710656)), (439/2251799813685248), by norm_num⟩
  | 16 => ⟨((-275983709/9007199254740992), (49877697/562949953421312)), (319/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (1239921789347/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222264977126495/79228162514264337593543950336), (2932739805725/633825300114114700748351602688)), (184977/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889011718399065/39614081257132168796771975168), (824653287657/9903520314283042199192993792)), (208137/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888741069945979/2475880078570760549798248448), (3503884702985/2475880078570760549798248448)), (55297/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885203610042881/77371252455336267181195264), (3502881795637/154742504910672534362390528)), (221237/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548818819376637/9671406556917033397649408), (820721605635/2417851639229258349412352)), (207461/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629072899085939/302231454903657293676544), (2871460727931/604462909807314587353088)), (181581/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886747159291237/75557863725914323419136), (4664127794869/75557863725914323419136)), (73791/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648377808439987/2361183241434822606848), (874087556997/1180591620717411303424)), (110729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405092515020349/147573952589676412928), (4804646403197/590295810358705651712)), (304641/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227765828955027/9223372036854775808), (750194729215/9223372036854775808)), (381007/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821139821505965/9223372036854775808), (210809773545/288230376151711744)), (428917/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592387591828831/1152921504606846976), (3369309625129/576460752303423488)), (53659/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193181454571985/144115188075855872), (184002976665/4503599627370496)), (376013/144115188075855872), by norm_num⟩
  | 4 => ⟨((744768402761917/18014398509481984), (8815771183557/36028797018963968)), (564819/36028797018963968), by norm_num⟩
  | 3 => ⟨((185828638119787/1125899906842624), (2747777952075/2251799813685248)), (353713/4503599627370496), by norm_num⟩
  | 2 => ⟨((555670637224947/1125899906842624), (21896610073905/4503599627370496)), (354767/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104092436320885/1125899906842624), (32631555664847/2251799813685248)), (534793/562949953421312), by norm_num⟩
  | 0 => ⟨((2164815326820419/2251799813685248), (16103428027659/562949953421312)), (1080201/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164815326820419/2251799813685248), (16103428027659/562949953421312)), (4120639803172874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1039674185172307/1125899906842624), (123850966135655/2251799813685248)), (4277495/1125899906842624), by norm_num⟩
  | 2 => ⟨((478323001589461/562949953421312), (228731970785905/2251799813685248)), (16740697/2251799813685248), by norm_num⟩
  | 3 => ⟨((1602437288254253/2251799813685248), (194347227779067/1125899906842624)), (31849169/2251799813685248), by norm_num⟩
  | 4 => ⟨((536620055725747/1125899906842624), (553209468744633/2251799813685248)), (14081157/562949953421312), by norm_num⟩
  | 5 => ⟨((187806130762457/1125899906842624), (32958446632509/140737488355328)), (162730575/4503599627370496), by norm_num⟩
  | 6 => ⟨((-486713905891965/18014398509481984), (175924649795219/2251799813685248)), (261012825/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1233032703/16777216)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-628048891/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((613539328626675/9007199254740992), (717255650414689/18014398509481984)), (275731293/18014398509481984), by norm_num⟩
  | 1 => ⟨((-861420209/4294967296), (-125879973/1073741824)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((317049905/1073741824), (370645899/2147483648)), (291/4294967296), by norm_num⟩
  | 3 => ⟨((-1244712131/4294967296), (-363781411/2147483648)), (9/134217728), by norm_num⟩
  | 4 => ⟨((916244729/4294967296), (535566083/4294967296)), (107/2147483648), by norm_num⟩
  | 5 => ⟨((-539565339/4294967296), (-157694165/2147483648)), (127/4294967296), by norm_num⟩
  | 6 => ⟨((1059144811/17179869184), (309547231/8589934592)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((-891024933/34359738368), (-520824533/34359738368)), (107/17179869184), by norm_num⟩
  | 8 => ⟨((81986517/8589934592), (191692007/34359738368)), (317/137438953472), by norm_num⟩
  | 9 => ⟨((-858326387/274877906944), (-250855741/137438953472)), (209/274877906944), by norm_num⟩
  | 10 => ⟨((252728967/274877906944), (295451769/549755813888)), (31/137438953472), by norm_num⟩
  | 11 => ⟨((-1082392759/4398046511104), (-316341711/2199023255552)), (67/1099511627776), by norm_num⟩
  | 12 => ⟨((1062346477/17592186044416), (310482955/8796093022208)), (265/17592186044416), by norm_num⟩
  | 13 => ⟨((-481232981/35184372088832), (-562583455/70368744177664)), (121/35184372088832), by norm_num⟩
  | 14 => ⟨((202423021/70368744177664), (473283615/281474976710656)), (205/281474976710656), by norm_num⟩
  | 15 => ⟨((-635757049/1125899906842624), (-371614593/1125899906842624)), (81/562949953421312), by norm_num⟩
  | 16 => ⟨((467986959/4503599627370496), (273549123/4503599627370496)), (15/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (689031525791/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889026117865213/316912650057057350374175801344), (814807261625/633825300114114700748351602688)), (184561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888935941892727/39614081257132168796771975168), (458228547405/19807040628566084398385987584)), (207641/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944330445722751/1237940039285380274899124224), (973483533705/2475880078570760549798248448)), (220631/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770327416996163/154742504910672534362390528), (243300005925/38685626227668133590597632)), (220645/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774372201279883/4835703278458516698824704), (228018477011/2417851639229258349412352)), (206869/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314520270426325/151115727451828646838272), (797763685029/604462909807314587353088)), (181025/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886642741044555/75557863725914323419136), (647900958807/37778931862957161709568)), (18387/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((81042372203233/295147905179352825856), (971358151713/4722366482869645213696)), (220667/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810132166808623/295147905179352825856), (667408191897/295147905179352825856)), (9483/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821996058668619/73786976294838206464), (1667319769423/73786976294838206464)), (189689/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820995102698399/9223372036854775808), (1874085228253/9223372036854775808)), (3335/72057594037927936), by norm_num⟩
  | 6 => ⟨((199030698394041/144115188075855872), (936012766083/576460752303423488)), (426979/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596530123094255/72057594037927936), (1635708196261/144115188075855872)), (46715/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489361065179377/36028797018963968), (1224470764687/18014398509481984)), (140201/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486420012862227/9007199254740992), (47704804257/140737488355328)), (701401/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111147971465463/2251799813685248), (6082074080749/4503599627370496)), (1403995/4503599627370496), by norm_num⟩
  | 1 => ⟨((275960413780945/281474976710656), (9062994400231/2251799813685248)), (1054499/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164122012077881/2251799813685248), (17886929380555/2251799813685248)), (4230131/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164122012077881/2251799813685248), (17886929380555/2251799813685248)), (16136669167525481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079716017585543/2251799813685248), (17190470203295/1125899906842624)), (8198051/2251799813685248), by norm_num⟩
  | 2 => ⟨((960129012903239/1125899906842624), (31753529789231/1125899906842624)), (15393443/2251799813685248), by norm_num⟩
  | 3 => ⟨((1635739427933331/2251799813685248), (108313305747487/2251799813685248)), (27122283/2251799813685248), by norm_num⟩
  | 4 => ⟨((1183014443692493/2251799813685248), (157360653202121/2251799813685248)), (42013231/2251799813685248), by norm_num⟩
  | 5 => ⟨((152629109218967/562949953421312), (165343228537113/2251799813685248)), (50016427/2251799813685248), by norm_num⟩
  | 6 => ⟨((613539328626675/9007199254740992), (717255650414689/18014398509481984)), (275731293/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-628048891/8388608)), (1/8388608), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1277979503/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((485603687905013/9007199254740992), (-237942533996151/4503599627370496)), (77488745/9007199254740992), by norm_num⟩
  | 1 => ⟨((-693673439/4294967296), (679790619/4294967296)), (7/268435456), by norm_num⟩
  | 2 => ⟨((519514977/2147483648), (-254558837/1073741824)), (85/2147483648), by norm_num⟩
  | 3 => ⟨((-64846991/268435456), (1016786831/4294967296)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((777056895/4294967296), (-761505281/4294967296)), (131/4294967296), by norm_num⟩
  | 5 => ⟨((-116392721/1073741824), (912506379/8589934592)), (159/8589934592), by norm_num⟩
  | 6 => ⟨((929817149/17179869184), (-455604135/8589934592)), (161/17179869184), by norm_num⟩
  | 7 => ⟨((-795852355/34359738368), (389962289/17179869184)), (139/34359738368), by norm_num⟩
  | 8 => ⟨((298020073/34359738368), (-584111307/68719476736)), (53/34359738368), by norm_num⟩
  | 9 => ⟨((-793589645/274877906944), (777707153/274877906944)), (143/274877906944), by norm_num⟩
  | 10 => ⟨((950952845/1099511627776), (-931920967/1099511627776)), (173/1099511627776), by norm_num⟩
  | 11 => ⟨((-129490915/549755813888), (507597403/2199023255552)), (191/4398046511104), by norm_num⟩
  | 12 => ⟨((1034453635/17592186044416), (-1013750615/17592186044416)), (193/17592186044416), by norm_num⟩
  | 13 => ⟨((-953521889/70368744177664), (934438595/70368744177664)), (45/17592186044416), by norm_num⟩
  | 14 => ⟨((816141799/281474976710656), (-799807959/281474976710656)), (39/70368744177664), by norm_num⟩
  | 15 => ⟨((-651984621/1125899906842624), (319468069/562949953421312)), (127/1125899906842624), by norm_num⟩
  | 16 => ⟨((488292843/4503599627370496), (-957040805/9007199254740992)), (193/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-504951297353/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888991840968397/316912650057057350374175801344), (-298540708973/158456325028528675187087900672)), (46159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888858813410447/39614081257132168796771975168), (-671566685097/19807040628566084398385987584)), (103865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944289466872747/1237940039285380274899124224), (-44584475941/77371252455336267181195264)), (55183/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885122724775057/77371252455336267181195264), (-1426280459137/154742504910672534362390528)), (13797/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548667547742691/9671406556917033397649408), (-1336688908345/9671406556917033397649408)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((629006911712549/302231454903657293676544), (-1169153966355/604462909807314587353088)), (90563/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943266713521499/37778931862957161709568), (-1899034053289/75557863725914323419136)), (9199/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((40518623528475/147573952589676412928), (-1423539951755/4722366482869645213696)), (110405/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810075776559517/295147905179352825856), (-1956172873093/590295810358705651712)), (151835/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821855042272635/73786976294838206464), (-610856399379/18446744073709551616)), (189835/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910418201713927/4611686018427387904), (-1373197027615/4611686018427387904)), (213623/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796043409228487/576460752303423488), (-2743322655177/1152921504606846976)), (213695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192921245966329/144115188075855872), (-2396956499505/144115188075855872)), (187065/144115188075855872), by norm_num⟩
  | 4 => ⟨((744576205419183/18014398509481984), (-3588544339443/36028797018963968)), (140381/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486158928158225/9007199254740992), (-1118411862383/2251799813685248)), (351241/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221772984089799/4503599627370496), (-4455648366103/2251799813685248)), (703349/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206896936359917/2251799813685248), (-13277301379501/2251799813685248)), (528601/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081270873999139/1125899906842624), (-6549532617743/562949953421312)), (530797/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081270873999139/1125899906842624), (-6549532617743/562949953421312)), (2024829866649436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((259564618121115/281474976710656), (-1572479670447/70368744177664)), (4127461/2251799813685248), by norm_num⟩
  | 2 => ⟨((1913753860189239/2251799813685248), (-92804858732687/2251799813685248)), (487301/140737488355328), by norm_num⟩
  | 3 => ⟨((811315702527975/1125899906842624), (-39436377861967/562949953421312)), (13895347/2251799813685248), by norm_num⟩
  | 4 => ⟨((1158206433112551/2251799813685248), (-227340653752893/2251799813685248)), (21972607/2251799813685248), by norm_num⟩
  | 5 => ⟨((572767774922103/2251799813685248), (-233863957252657/2251799813685248)), (27039777/2251799813685248), by norm_num⟩
  | 6 => ⟨((485603687905013/9007199254740992), (-237942533996151/4503599627370496)), (77488745/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1277979503/16777216)), (1/16777216), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1298793389/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-280670027682051/9007199254740992), (-1176753925393887/18014398509481984)), (466240203/18014398509481984), by norm_num⟩
  | 1 => ⟨((407460307/4294967296), (213542803/1073741824)), (85/1073741824), by norm_num⟩
  | 2 => ⟨((-19383157/134217728), (-650135855/2147483648)), (65/536870912), by norm_num⟩
  | 3 => ⟨((314733101/2147483648), (1319568799/4294967296)), (265/2147483648), by norm_num⟩
  | 4 => ⟨((-239552997/2147483648), (-251091051/1073741824)), (405/4294967296), by norm_num⟩
  | 5 => ⟨((145864895/2147483648), (611561871/4294967296)), (495/8589934592), by norm_num⟩
  | 6 => ⟨((-296059297/8589934592), (-310318973/4294967296)), (505/17179869184), by norm_num⟩
  | 7 => ⟨((32191399/2147483648), (1079740659/34359738368)), (221/17179869184), by norm_num⟩
  | 8 => ⟨((-196014873/34359738368), (-410911833/34359738368)), (169/34359738368), by norm_num⟩
  | 9 => ⟨((530463715/274877906944), (556013465/137438953472)), (115/68719476736), by norm_num⟩
  | 10 => ⟨((-646003473/1099511627776), (-169279547/137438953472)), (281/549755813888), by norm_num⟩
  | 11 => ⟨((178797461/1099511627776), (749636915/2199023255552)), (313/2199023255552), by norm_num⟩
  | 12 => ⟨((-362901921/8796093022208), (-95095267/1099511627776)), (319/8796093022208), by norm_num⟩
  | 13 => ⟨((339957859/35184372088832), (1425327627/70368744177664)), (75/8796093022208), by norm_num⟩
  | 14 => ⟨((-591433903/281474976710656), (-1239840555/281474976710656)), (131/70368744177664), by norm_num⟩
  | 15 => ⟨((240084505/562949953421312), (1006592637/1125899906842624)), (427/1125899906842624), by norm_num⟩
  | 16 => ⟨((-365471331/4503599627370496), (-766148467/4503599627370496)), (327/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-1312964092725/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777914462031291/633825300114114700748351602688), (-3104822090405/633825300114114700748351602688)), (185011/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888780716057439/39614081257132168796771975168), (-873031187891/9903520314283042199192993792)), (104089/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472123913260617/618970019642690137449562112), (-927347032123/618970019642690137449562112)), (110617/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770161829198185/154742504910672534362390528), (-3708269799277/154742504910672534362390528)), (221285/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548588793087235/9671406556917033397649408), (-868828774141/2417851639229258349412352)), (207509/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157243069108177/75557863725914323419136), (-3039713301665/604462909807314587353088)), (90813/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943210093830673/37778931862957161709568), (-4937308644191/75557863725914323419136)), (73811/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648255216856551/2361183241434822606848), (-3701035114383/4722366482869645213696)), (110761/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620033007369961/590295810358705651712), (-635720269299/73786976294838206464)), (152369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821705427166723/73786976294838206464), (-6352464012313/73786976294838206464)), (381141/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820666119996321/9223372036854775808), (-7140011218765/9223372036854775808)), (107271/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795957041355553/576460752303423488), (-7131880057185/1152921504606846976)), (107365/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192767351203875/144115188075855872), (-1557814392167/36028797018963968)), (376201/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488916086357427/36028797018963968), (-4664318279673/18014398509481984)), (282575/18014398509481984), by norm_num⟩
  | 3 => ⟨((371463493132717/2251799813685248), (-11628915137253/9007199254740992)), (707923/9007199254740992), by norm_num⟩
  | 2 => ⟨((34705228101085/70368744177664), (-5790603657279/1125899906842624)), (1420313/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205868784571801/2251799813685248), (-34505872767363/2251799813685248)), (267709/281474976710656), by norm_num⟩
  | 0 => ⟨((1080103403438889/1125899906842624), (-68065478812279/2251799813685248)), (4328355/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080103403438889/1125899906842624), (-68065478812279/2251799813685248)), (16511363991744231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035140981614533/1125899906842624), (-130593767483305/2251799813685248)), (8566263/2251799813685248), by norm_num⟩
  | 2 => ⟨((1895822465754421/2251799813685248), (-240133176748373/2251799813685248)), (8372539/1125899906842624), by norm_num⟩
  | 3 => ⟨((6134812933843/8796093022208), (-404343111217769/2251799813685248)), (31767251/2251799813685248), by norm_num⟩
  | 4 => ⟨((1022744084714959/2251799813685248), (-282008084969799/1125899906842624)), (13930129/562949953421312), by norm_num⟩
  | 5 => ⟨((646497276038809/4503599627370496), (-512340571291957/2251799813685248)), (39264193/1125899906842624), by norm_num⟩
  | 6 => ⟨((-280670027682051/9007199254740992), (-1176753925393887/18014398509481984)), (466240203/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1298793389/16777216)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile034Terms2

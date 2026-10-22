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
namespace Reinmann.XiBand97.Tile045Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨45,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (7297/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (7297/256))
  have he : value ((69/80), (7297/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1478186551/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1239866883735425/18014398509481984), (-177494461116857/18014398509481984)), (89169111/9007199254740992), by norm_num⟩
  | 1 => ⟨((-228433679/1073741824), (16350833/536870912)), (265/8589934592), by norm_num⟩
  | 2 => ⟨((1412196399/4294967296), (-50541119/1073741824)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((-1455053007/4294967296), (208299659/4294967296)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((562203827/2147483648), (-40241443/1073741824)), (21/536870912), by norm_num⟩
  | 5 => ⟨((-1390236717/8589934592), (99510407/4294967296)), (105/4294967296), by norm_num⟩
  | 6 => ⟨((179053363/2147483648), (-205060595/17179869184)), (109/8589934592), by norm_num⟩
  | 7 => ⟨((-1265054963/34359738368), (181100287/34359738368)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((977584649/68719476736), (-139947169/68719476736)), (151/68719476736), by norm_num⟩
  | 9 => ⟨((-83937657/17179869184), (192258951/274877906944)), (209/274877906944), by norm_num⟩
  | 10 => ⟨((207563889/137438953472), (-29714029/137438953472)), (65/274877906944), by norm_num⟩
  | 11 => ⟨((-466610031/1099511627776), (133596109/2199023255552)), (295/4398046511104), by norm_num⟩
  | 12 => ⟨((961540943/8796093022208), (-137650415/8796093022208)), (77/4398046511104), by norm_num⟩
  | 13 => ⟨((-1829023923/70368744177664), (130917931/35184372088832)), (37/8796093022208), by norm_num⟩
  | 14 => ⟨((807655799/140737488355328), (-231241647/281474976710656)), (33/35184372088832), by norm_num⟩
  | 15 => ⟨((-1331465793/1125899906842624), (190607399/1125899906842624)), (55/281474976710656), by norm_num⟩
  | 16 => ⟨((1028904323/4503599627370496), (-147293891/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-92609164617/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777857810908691/633825300114114700748351602688), (-218982319623/633825300114114700748351602688)), (184443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944358640649143/19807040628566084398385987584), (-246298594569/39614081257132168796771975168)), (207503/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236053581316749/309485009821345068724781056), (-261621134051/2475880078570760549798248448)), (110237/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885047636367727/77371252455336267181195264), (-65385290675/38685626227668133590597632)), (110239/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774263434977551/4835703278458516698824704), (-245109905041/9671406556917033397649408)), (103351/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257890843257733/604462909807314587353088), (-214386270833/604462909807314587353088)), (45217/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886333795783921/75557863725914323419136), (-348218592601/75557863725914323419136)), (146959/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296446414372245/4722366482869645213696), (-130512408365/2361183241434822606848)), (110223/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619946237783655/590295810358705651712), (-179341597607/295147905179352825856)), (303123/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821598847785359/73786976294838206464), (-448015372941/73786976294838206464)), (47365/9223372036854775808), by norm_num⟩
  | 7 => ⟨((14223037515993/72057594037927936), (-125888032479/2305843009213693952)), (106577/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591799987507027/1152921504606846976), (-125742833105/288230376151711744)), (13323/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192671133778957/144115188075855872), (-439447422717/144115188075855872)), (373077/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488778967752025/36028797018963968), (-328934202223/18014398509481984)), (559679/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485695133081915/9007199254740992), (-205015199215/2251799813685248)), (349857/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220854379170177/4503599627370496), (-1633317693513/4503599627370496)), (1399777/4503599627370496), by norm_num⟩
  | 1 => ⟨((551385337182771/562949953421312), (-2433037370609/2251799813685248)), (525141/562949953421312), by norm_num⟩
  | 0 => ⟨((33748734315825/35184372088832), (-4798739874491/2251799813685248)), (4204843/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((33748734315825/35184372088832), (-4798739874491/2251799813685248)), (16040203103072356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071776990984609/2251799813685248), (-9205871099025/2251799813685248)), (4042233/1125899906842624), by norm_num⟩
  | 2 => ⟨((119131791995479/140737488355328), (-4234948375299/562949953421312)), (14942391/2251799813685248), by norm_num⟩
  | 3 => ⟨((1613359806904127/2251799813685248), (-28678470525717/2251799813685248)), (25521757/2251799813685248), by norm_num⟩
  | 4 => ⟨((1155567824478799/2251799813685248), (-20547426724383/1125899906842624)), (18610759/1125899906842624), by norm_num⟩
  | 5 => ⟨((1184517559585431/4503599627370496), (-84355438895517/4503599627370496)), (19780445/1125899906842624), by norm_num⟩
  | 6 => ⟨((1239866883735425/18014398509481984), (-177494461116857/18014398509481984)), (89169111/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1478186551/16777216)), (1/8388608), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-187430513/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((96947275497297/9007199254740992), (-1189698624354287/18014398509481984)), (371582649/18014398509481984), by norm_num⟩
  | 1 => ⟨((-144947825/4294967296), (1778742387/8589934592)), (279/4294967296), by norm_num⟩
  | 2 => ⟨((227241533/4294967296), (-348577279/1073741824)), (55/536870912), by norm_num⟩
  | 3 => ⟨((-237504837/4294967296), (1457282723/4294967296)), (231/2147483648), by norm_num⟩
  | 4 => ⟨((186173761/4294967296), (-1142325387/4294967296)), (91/1073741824), by norm_num⟩
  | 5 => ⟨((-58374675/2147483648), (1432701857/8589934592)), (459/8589934592), by norm_num⟩
  | 6 => ⟨((3813197/268435456), (-748704731/8589934592)), (241/8589934592), by norm_num⟩
  | 7 => ⟨((-109314351/17179869184), (1341462487/34359738368)), (217/17179869184), by norm_num⟩
  | 8 => ⟨((85688629/34359738368), (-1051536967/68719476736)), (171/34359738368), by norm_num⟩
  | 9 => ⟨((-238823289/274877906944), (1465372479/274877906944)), (479/274877906944), by norm_num⟩
  | 10 => ⟨((9360363/34359738368), (-1837866773/1099511627776)), (603/1099511627776), by norm_num⟩
  | 11 => ⟨((-667031/8589934592), (523874603/1099511627776)), (173/1099511627776), by norm_num⟩
  | 12 => ⟨((22309033/1099511627776), (-1095070525/8796093022208)), (363/8796093022208), by norm_num⟩
  | 13 => ⟨((-172184231/35184372088832), (1056488399/35184372088832)), (11/1099511627776), by norm_num⟩
  | 14 => ⟨((154252189/140737488355328), (-236615233/35184372088832)), (317/140737488355328), by norm_num⟩
  | 15 => ⟨((-128975159/562949953421312), (395683037/281474976710656)), (133/281474976710656), by norm_num⟩
  | 16 => ⟨((12637527/281474976710656), (-620330937/2251799813685248)), (419/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1835690982183/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888898133237617/316912650057057350374175801344), (-1085093497065/316912650057057350374175801344)), (184827/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944323961339579/19807040628566084398385987584), (-305111162417/4951760157141521099596496896)), (207959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944177396551319/1237940039285380274899124224), (-324091190031/309485009821345068724781056)), (55247/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770021231155665/154742504910672534362390528), (-2591925105417/154742504910672534362390528)), (6907/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774228630244019/4835703278458516698824704), (-75908606787/302231454903657293676544)), (12953/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628914869840717/302231454903657293676544), (-531146745691/151115727451828646838272)), (181381/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471558534177351/18889465931478580854784), (-3450853351997/75557863725914323419136)), (147407/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296371350433963/4722366482869645213696), (-2586740349135/4722366482869645213696)), (221173/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619842506234321/590295810358705651712), (-3554494964327/590295810358705651712)), (304215/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821468406740597/73786976294838206464), (-2219855849803/36893488147419103232)), (190211/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820400990215367/9223372036854775808), (-1247498779363/2305843009213693952)), (428185/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591650846869279/1152921504606846976), (-1246037640983/288230376151711744)), (13389/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192539145294429/144115188075855872), (-2177282518517/72057594037927936)), (375189/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488578015347819/36028797018963968), (-3259367578787/18014398509481984)), (563377/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485438770717409/9007199254740992), (-8125519462695/9007199254740992)), (352631/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220326238824969/4503599627370496), (-16182528965749/4503599627370496)), (176707/562949953421312), by norm_num⟩
  | 1 => ⟨((551177736874373/562949953421312), (-24103176678065/2251799813685248)), (266043/281474976710656), by norm_num⟩
  | 0 => ⟨((539526877137267/562949953421312), (-47527822288939/2251799813685248)), (2144145/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539526877137267/562949953421312), (-47527822288939/2251799813685248)), (8179264072898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((258413797280773/281474976710656), (-91100593865741/2251799813685248)), (8400751/2251799813685248), by norm_num⟩
  | 2 => ⟨((947125240858091/1125899906842624), (-167273486762409/2251799813685248)), (8052347/1125899906842624), by norm_num⟩
  | 3 => ⟨((395262097286723/562949953421312), (-17589145855259/140737488355328)), (14743857/1125899906842624), by norm_num⟩
  | 4 => ⟨((134365475830849/281474976710656), (-98798447541977/562949953421312)), (48778869/2251799813685248), by norm_num⟩
  | 5 => ⟨((887541647561777/4503599627370496), (-377301046663857/2251799813685248)), (127383749/4503599627370496), by norm_num⟩
  | 6 => ⟨((96947275497297/9007199254740992), (-1189698624354287/18014398509481984)), (371582649/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-187430513/2097152)), (1/8388608), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-23746825/262144)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-252200537012301/4503599627370496), (-576582087499213/18014398509481984)), (105670215/4503599627370496), by norm_num⟩
  | 1 => ⟨((47773533/268435456), (436880329/4294967296)), (161/2147483648), by norm_num⟩
  | 2 => ⟨((-303653719/1073741824), (-694214601/4294967296)), (257/2147483648), by norm_num⟩
  | 3 => ⟨((1286703819/4294967296), (183854281/1073741824)), (547/4294967296), by norm_num⟩
  | 4 => ⟨((-255575875/1073741824), (-292149401/2147483648)), (109/1073741824), by norm_num⟩
  | 5 => ⟨((1299574221/8589934592), (371386609/4294967296)), (139/2147483648), by norm_num⟩
  | 6 => ⟨((-688352805/8589934592), (-196714439/4294967296)), (37/1073741824), by norm_num⟩
  | 7 => ⟨((312517467/8589934592), (22327467/1073741824)), (135/8589934592), by norm_num⟩
  | 8 => ⟨((-993197333/68719476736), (-17739473/2147483648)), (431/68719476736), by norm_num⟩
  | 9 => ⟨((175357477/34359738368), (50112889/17179869184)), (153/68719476736), by norm_num⟩
  | 10 => ⟨((-445836401/274877906944), (-127409167/137438953472)), (391/549755813888), by norm_num⟩
  | 11 => ⟨((128808371/274877906944), (294482321/1099511627776)), (227/1099511627776), by norm_num⟩
  | 12 => ⟨((-545813249/4398046511104), (-623920445/8796093022208)), (483/8796093022208), by norm_num⟩
  | 13 => ⟨((1067460853/35184372088832), (610108541/35184372088832)), (237/17592186044416), by norm_num⟩
  | 14 => ⟨((-121158859/17592186044416), (-553987939/140737488355328)), (27/8796093022208), by norm_num⟩
  | 15 => ⟨((821438669/562949953421312), (58686783/70368744177664)), (23/35184372088832), by norm_num⟩
  | 16 => ⟨((-652644077/2251799813685248), (-373019511/2251799813685248)), (587/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-3415908995131/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777733518008685/633825300114114700748351602688), (-504763041645/79228162514264337593543950336)), (185195/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888577006922989/39614081257132168796771975168), (-1135443856725/9903520314283042199192993792)), (52099/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944139504085699/1237940039285380274899124224), (-4824285464541/2475880078570760549798248448)), (221481/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884972477626197/77371252455336267181195264), (-4822766091073/154742504910672534362390528)), (221547/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774192615311069/4835703278458516698824704), (-4519729349421/9671406556917033397649408)), (207771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314441548212487/151115727451828646838272), (-3953149851705/604462909807314587353088)), (181871/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943064948938101/37778931862957161709568), (-3210422323665/37778931862957161709568)), (295673/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296292319058451/4722366482869645213696), (-2406494368339/2361183241434822606848)), (13867/295147905179352825856), by norm_num⟩
  | 9 => ⟨((809866227602075/295147905179352825856), (-6613563914947/590295810358705651712)), (305263/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821328772148293/73786976294838206464), (-8260515204283/73786976294838206464)), (190931/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113765066229387/576460752303423488), (-4642115527967/4611686018427387904)), (214993/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397871843216929/288230376151711744), (-9273179404535/1152921504606846976)), (215237/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192392130932867/144115188075855872), (-7911729777/140737488355328)), (2947/1125899906842624), by norm_num⟩
  | 4 => ⟨((372087393493601/9007199254740992), (-6063803303685/18014398509481984)), (35433/2251799813685248), by norm_num⟩
  | 3 => ⟨((92821214079227/562949953421312), (-15116160013067/9007199254740992)), (710593/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219686429839871/4503599627370496), (-30102554519249/4503599627370496)), (713499/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101824678117579/1125899906842624), (-44830394889967/2251799813685248)), (1077537/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155582291774917/2251799813685248), (-22093224993047/562949953421312)), (1092181/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155582291774917/2251799813685248), (-22093224993047/562949953421312)), (4166339876415061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1030003914862323/1125899906842624), (-169193599799695/2251799813685248)), (4353505/1125899906842624), by norm_num⟩
  | 2 => ⟨((467959647067325/562949953421312), (-154782915518701/1125899906842624)), (17239259/2251799813685248), by norm_num⟩
  | 3 => ⟨((1513433243966191/2251799813685248), (-514661440705189/2251799813685248)), (33400657/2251799813685248), by norm_num⟩
  | 4 => ⟨((899548784524601/2251799813685248), (-691807263698123/2251799813685248)), (60164937/2251799813685248), by norm_num⟩
  | 5 => ⟨((36702943532663/562949953421312), (-552726205413855/2251799813685248)), (170075223/4503599627370496), by norm_num⟩
  | 6 => ⟨((-252200537012301/4503599627370496), (-576582087499213/18014398509481984)), (105670215/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-23746825/262144)), (1/8388608), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-384829635/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-896830684795313/18014398509481984), (673810260769579/18014398509481984)), (205910241/9007199254740992), by norm_num⟩
  | 1 => ⟨((344131781/2147483648), (-129277203/1073741824)), (159/2147483648), by norm_num⟩
  | 2 => ⟨((-1107717471/4294967296), (832254527/4294967296)), (257/2147483648), by norm_num⟩
  | 3 => ⟨((297133749/1073741824), (-892974659/4294967296)), (277/2147483648), by norm_num⟩
  | 4 => ⟨((-478218321/2147483648), (179648409/1073741824)), (7/67108864), by norm_num⟩
  | 5 => ⟨((615730157/4294967296), (-462612737/4294967296)), (145/2147483648), by norm_num⟩
  | 6 => ⟨((-165163243/2147483648), (496364319/8589934592)), (313/8589934592), by norm_num⟩
  | 7 => ⟨((1215177075/34359738368), (-456495745/17179869184)), (289/17179869184), by norm_num⟩
  | 8 => ⟨((-244469007/17179869184), (734701559/68719476736)), (467/68719476736), by norm_num⟩
  | 9 => ⟨((699480335/137438953472), (-262768121/68719476736)), (21/8589934592), by norm_num⟩
  | 10 => ⟨((-112577017/68719476736), (338327181/274877906944)), (217/274877906944), by norm_num⟩
  | 11 => ⟨((527085729/1099511627776), (-396012067/1099511627776)), (255/1099511627776), by norm_num⟩
  | 12 => ⟨((-1131082341/8796093022208), (849809113/8796093022208)), (275/4398046511104), by norm_num⟩
  | 13 => ⟨((280062585/8796093022208), (-210417693/8796093022208)), (547/35184372088832), by norm_num⟩
  | 14 => ⟨((-1030270497/140737488355328), (193516693/35184372088832)), (505/140737488355328), by norm_num⟩
  | 15 => ⟨((884350079/562949953421312), (-664433285/562949953421312)), (435/562949953421312), by norm_num⟩
  | 16 => ⟨((-711653273/2251799813685248), (133670515/562949953421312)), (11/70368744177664), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (3252940216189/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777680116815071/633825300114114700748351602688), (480653461247/79228162514264337593543950336)), (92579/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944258495112617/19807040628566084398385987584), (2162415556347/19807040628566084398385987584)), (208351/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944107659210877/1237940039285380274899124224), (4593830425241/2475880078570760549798248448)), (110715/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769881353172545/154742504910672534362390528), (4592365419505/154742504910672534362390528)), (221493/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548325696759505/9671406556917033397649408), (537973312175/1208925819614629174706176)), (207717/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257714193737745/604462909807314587353088), (470532205901/75557863725914323419136)), (45455/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943022786789493/37778931862957161709568), (1528500800417/18889465931478580854784)), (295585/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648114614082665/2361183241434822606848), (1145738129781/1180591620717411303424)), (27725/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404911488121261/147573952589676412928), (6297418327173/590295810358705651712)), (305155/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455305253538357/18446744073709551616), (3932782314443/36893488147419103232)), (381713/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227515042555623/1152921504606846976), (8840229995553/9223372036854775808)), (53725/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397841822028147/288230376151711744), (2207394121891/288230376151711744)), (215133/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192287768932019/144115188075855872), (7713906953851/144115188075855872)), (23563/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488194451250779/36028797018963968), (11546947280773/36028797018963968)), (283281/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484947998268603/9007199254740992), (3597976897601/2251799813685248)), (710043/9007199254740992), by norm_num⟩
  | 2 => ⟨((554827742202241/1125899906842624), (28658771465991/4503599627370496)), (1425623/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203104520558783/2251799813685248), (42676547407191/2251799813685248)), (2152321/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077282643607695/1125899906842624), (10514080707609/281474976710656)), (4360443/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077282643607695/1125899906842624), (10514080707609/281474976710656)), (16633769997603606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((514596880631209/562949953421312), (80480593992133/1125899906842624)), (2167517/562949953421312), by norm_num⟩
  | 2 => ⟨((467520543262337/562949953421312), (73567929738691/562949953421312)), (17090245/2251799813685248), by norm_num⟩
  | 3 => ⟨((757307880712239/1125899906842624), (488775505091869/2251799813685248)), (32853133/2251799813685248), by norm_num⟩
  | 4 => ⟨((912674118670527/2251799813685248), (657524775791489/2251799813685248)), (14614461/562949953421312), by norm_num⟩
  | 5 => ⟨((355835553122019/4503599627370496), (266500530643269/1125899906842624)), (20381573/562949953421312), by norm_num⟩
  | 6 => ⟨((-896830684795313/18014398509481984), (673810260769579/18014398509481984)), (205910241/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-384829635/4194304)), (1/8388608), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-194759315/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((103198932351747/9007199254740992), (1064616640555379/18014398509481984)), (331267161/18014398509481984), by norm_num⟩
  | 1 => ⟨((-320655903/8589934592), (-206746089/1073741824)), (517/8589934592), by norm_num⟩
  | 2 => ⟨((65295493/1073741824), (673598717/2147483648)), (423/4294967296), by norm_num⟩
  | 3 => ⟨((-141826013/2147483648), (-1463099765/4294967296)), (231/2147483648), by norm_num⟩
  | 4 => ⟨((231041421/4294967296), (595865035/2147483648)), (189/2147483648), by norm_num⟩
  | 5 => ⟨((-150551051/4294967296), (-776554323/4294967296)), (495/8589934592), by norm_num⟩
  | 6 => ⟨((81751643/4294967296), (105420373/1073741824)), (135/4294967296), by norm_num⟩
  | 7 => ⟨((-304405423/34359738368), (-1570147439/34359738368)), (505/34359738368), by norm_num⟩
  | 8 => ⟨((61986391/17179869184), (159865373/8589934592)), (413/68719476736), by norm_num⟩
  | 9 => ⟨((-44879477/34359738368), (-925967677/137438953472)), (301/137438953472), by norm_num⟩
  | 10 => ⟨((116977335/274877906944), (1206756833/549755813888)), (197/274877906944), by norm_num⟩
  | 11 => ⟨((-277180691/2199023255552), (-1429720095/2199023255552)), (469/2199023255552), by norm_num⟩
  | 12 => ⟨((150513575/4398046511104), (1552722031/8796093022208)), (511/8796093022208), by norm_num⟩
  | 13 => ⟨((-150888541/17592186044416), (-778295119/17592186044416)), (257/17592186044416), by norm_num⟩
  | 14 => ⟨((70229919/35184372088832), (362251519/35184372088832)), (15/4398046511104), by norm_num⟩
  | 15 => ⟨((-122035123/281474976710656), (-1258933781/562949953421312)), (419/562949953421312), by norm_num⟩
  | 16 => ⟨((99400553/1125899906842624), (1025431949/2251799813685248)), (343/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (56146686107/316912650057057350374175801344)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777633543462171/633825300114114700748351602688), (1061856465235/316912650057057350374175801344)), (92409/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236058113650015/4951760157141521099596496896), (298574757215/4951760157141521099596496896)), (51987/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472040100959453/618970019642690137449562112), (1268579054259/1237940039285380274899124224)), (13811/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769826912236635/154742504910672534362390528), (2536340262357/154742504910672534362390528)), (221011/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548275161215363/9671406556917033397649408), (297118797237/1208925819614629174706176)), (51809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314417619374929/151115727451828646838272), (2078963349109/604462909807314587353088)), (22671/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((117873467226535/4722366482869645213696), (1688344164547/37778931862957161709568)), (294793/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648088738508841/2361183241434822606848), (2531093343275/4722366482869645213696)), (221157/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202447016131889/73786976294838206464), (1738971333137/295147905179352825856)), (152095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821135733195809/73786976294838206464), (4343965000569/73786976294838206464)), (380387/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820027141767923/9223372036854775808), (2441101454809/4611686018427387904)), (428141/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795638754745951/576460752303423488), (4876262307287/1152921504606846976)), (428399/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192213049297039/144115188075855872), (532506915947/18014398509481984)), (93785/36028797018963968), by norm_num⟩
  | 4 => ⟨((2906425816219/70368744177664), (6376757044955/36028797018963968)), (563291/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484830776192147/9007199254740992), (7947676300055/9007199254740992)), (352567/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219116239887803/4503599627370496), (7912871887901/2251799813685248)), (706669/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202910865949725/2251799813685248), (23565295957547/2251799813685248)), (2127711/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154566663221203/2251799813685248), (46441512651221/2251799813685248)), (4286415/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154566663221203/2251799813685248), (46441512651221/2251799813685248)), (16351375588423918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060574241088105/2251799813685248), (88872318347099/2251799813685248)), (4189731/1125899906842624), by norm_num⟩
  | 2 => ⟨((1882080231249109/2251799813685248), (162650346464067/2251799813685248)), (15997165/2251799813685248), by norm_num⟩
  | 3 => ⟨((780657951982859/1125899906842624), (67972516878587/562949953421312)), (14526111/1125899906842624), by norm_num⟩
  | 4 => ⟨((1049730588304301/2251799813685248), (188518661366139/1125899906842624)), (47303235/2251799813685248), by norm_num⟩
  | 5 => ⟨((213113341482567/1125899906842624), (703060029047067/4503599627370496)), (119887637/4503599627370496), by norm_num⟩
  | 6 => ⟨((103198932351747/9007199254740992), (1064616640555379/18014398509481984)), (331267161/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-194759315/2097152)), (1/8388608), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1576122555/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1001715382285355/18014398509481984), (156886300625509/9007199254740992)), (172313031/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1574273341/8589934592), (-123279489/2147483648)), (273/8589934592), by norm_num⟩
  | 2 => ⟨((1297137029/4294967296), (406309085/4294967296)), (227/4294967296), by norm_num⟩
  | 3 => ⟨((-178131335/536870912), (-223188077/2147483648)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((587091821/2147483648), (183897873/2147483648)), (209/4294967296), by norm_num⟩
  | 5 => ⟨((-773983547/4294967296), (-60609739/1073741824)), (139/4294967296), by norm_num⟩
  | 6 => ⟨((212576959/2147483648), (16646651/536870912)), (77/4294967296), by norm_num⟩
  | 7 => ⟨((-200176851/4294967296), (-501619621/34359738368)), (73/8589934592), by norm_num⟩
  | 8 => ⟨((659750245/34359738368), (206657055/34359738368)), (243/68719476736), by norm_num⟩
  | 9 => ⟨((-966412969/137438953472), (-18919665/8589934592)), (45/34359738368), by norm_num⟩
  | 10 => ⟨((318513949/137438953472), (99769807/137438953472)), (239/549755813888), by norm_num⟩
  | 11 => ⟨((-381734551/549755813888), (-478290921/2199023255552)), (289/2199023255552), by norm_num⟩
  | 12 => ⟨((838756537/4398046511104), (131364071/2199023255552)), (161/4398046511104), by norm_num⟩
  | 13 => ⟨((-850586067/17592186044416), (-8326049/549755813888)), (165/17592186044416), by norm_num⟩
  | 14 => ⟨((800969405/70368744177664), (250891879/70368744177664)), (313/140737488355328), by norm_num⟩
  | 15 => ⟨((-703963865/281474976710656), (-220506321/281474976710656)), (277/562949953421312), by norm_num⟩
  | 16 => ⟨((1160075029/2251799813685248), (363376431/2251799813685248)), (115/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (197706875651/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777585728777703/633825300114114700748351602688), (233679232633/316912650057057350374175801344)), (46123/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888411256322569/39614081257132168796771975168), (131412542503/9903520314283042199192993792)), (25945/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888103583558243/2475880078570760549798248448), (558341473343/2475880078570760549798248448)), (55135/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884885150422523/77371252455336267181195264), (558159514633/154742504910672534362390528)), (55137/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48381947181163/302231454903657293676544), (261540648725/4835703278458516698824704)), (51693/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((9825191047385/4722366482869645213696), (457502981873/604462909807314587353088)), (90467/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471475275631653/18889465931478580854784), (371540191411/37778931862957161709568)), (294033/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296122059869431/4722366482869645213696), (278496884751/2361183241434822606848)), (220539/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619500519008847/590295810358705651712), (382676233115/295147905179352825856)), (303263/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910521051006459/36893488147419103232), (238980071747/18446744073709551616)), (47389/9223372036854775808), by norm_num⟩
  | 7 => ⟨((909961508133497/4611686018427387904), (1074352228597/9223372036854775808)), (106637/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591174892505189/1152921504606846976), (1073031202661/1152921504606846976)), (213303/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192124951762847/144115188075855872), (468709167043/72057594037927936)), (373347/144115188075855872), by norm_num⟩
  | 4 => ⟨((92997577775923/2251799813685248), (1403165020747/36028797018963968)), (70019/4503599627370496), by norm_num⟩
  | 3 => ⟨((742337842585245/4503599627370496), (1748784187497/9007199254740992)), (87553/1125899906842624), by norm_num⟩
  | 2 => ⟨((554705894852173/1125899906842624), (217631312431/281474976710656)), (700779/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202515309944217/2251799813685248), (5184653632867/2251799813685248)), (1052067/1125899906842624), by norm_num⟩
  | 0 => ⟨((2153947088017215/2251799813685248), (10216334965847/2251799813685248)), (4215601/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153947088017215/2251799813685248), (10216334965847/2251799813685248)), (16081241616255950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060300234630977/2251799813685248), (19544761320395/2251799813685248)), (8103075/2251799813685248), by norm_num⟩
  | 2 => ⟨((942458346725547/1125899906842624), (4470654550361/281474976710656)), (3742149/562949953421312), by norm_num⟩
  | 3 => ⟨((788620677453367/1125899906842624), (59876096206527/2251799813685248)), (25535053/2251799813685248), by norm_num⟩
  | 4 => ⟨((275791072727027/562949953421312), (41939365361591/1125899906842624)), (18564653/1125899906842624), by norm_num⟩
  | 5 => ⟨((1074638876789763/4503599627370496), (164369887479607/4503599627370496)), (39145651/2251799813685248), by norm_num⟩
  | 6 => ⟨((1001715382285355/18014398509481984), (156886300625509/9007199254740992)), (172313031/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1576122555/16777216)), (1/8388608), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile045Terms3

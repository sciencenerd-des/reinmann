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
namespace Reinmann.XiBand97.Tile014Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26103/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26103/1280))
  have he : value ((69/80), (26103/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1057560739/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((613308303053451/9007199254740992), (-253349313663353/18014398509481984)), (188398647/18014398509481984), by norm_num⟩
  | 1 => ⟨((-451984883/2147483648), (46677201/1073741824)), (141/4294967296), by norm_num⟩
  | 2 => ⟨((698552231/2147483648), (-72140605/1073741824)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((-359875767/1073741824), (74329891/1073741824)), (229/4294967296), by norm_num⟩
  | 4 => ⟨((556195637/2147483648), (-229756849/4294967296)), (179/4294967296), by norm_num⟩
  | 5 => ⟨((-1375379461/8589934592), (142037635/4294967296)), (223/8589934592), by norm_num⟩
  | 6 => ⟨((88569923/1073741824), (-18293515/1073741824)), (29/2147483648), by norm_num⟩
  | 7 => ⟨((-1251535507/34359738368), (16156009/2147483648)), (207/34359738368), by norm_num⟩
  | 8 => ⟨((483568673/34359738368), (-199755639/68719476736)), (161/68719476736), by norm_num⟩
  | 9 => ⟨((-664325021/137438953472), (274423627/274877906944)), (223/274877906944), by norm_num⟩
  | 10 => ⟨((821382737/549755813888), (-339302033/1099511627776)), (139/549755813888), by norm_num⟩
  | 11 => ⟨((-923246877/2199023255552), (95345181/1099511627776)), (79/1099511627776), by norm_num⟩
  | 12 => ⟨((951265097/8796093022208), (-196477335/8796093022208)), (41/2199023255552), by norm_num⟩
  | 13 => ⟨((-904738707/35184372088832), (93433813/17592186044416)), (79/17592186044416), by norm_num⟩
  | 14 => ⟨((1598049001/281474976710656), (-41258269/35184372088832)), (141/140737488355328), by norm_num⟩
  | 15 => ⟨((-1317236615/1125899906842624), (34008283/140737488355328)), (235/1125899906842624), by norm_num⟩
  | 16 => ⟨((1017908575/4503599627370496), (-210242093/4503599627370496)), (183/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-33164346845/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444464445963773/158456325028528675187087900672), (-156839890111/316912650057057350374175801344)), (92231/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472179312345861/9903520314283042199192993792), (-352808792819/39614081257132168796771975168)), (51881/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944214307320951/1237940039285380274899124224), (-187378731271/1237940039285380274899124224)), (220499/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885047617307829/77371252455336267181195264), (-374642907319/154742504910672534362390528)), (220505/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387131707963197/2417851639229258349412352), (-351106060159/9671406556917033397649408)), (206729/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257890807555377/604462909807314587353088), (-307096192871/604462909807314587353088)), (90447/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943166866670951/37778931862957161709568), (-498803413367/75557863725914323419136)), (146981/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296446363672865/4722366482869645213696), (-186951632839/2361183241434822606848)), (220481/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809973080897685/295147905179352825856), (-64224169807/73786976294838206464)), (37897/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910799371700075/36893488147419103232), (-641756637547/73786976294838206464)), (378993/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455137167928365/2305843009213693952), (-721309887737/9223372036854775808)), (426399/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591799841084741/1152921504606846976), (-720477917927/1152921504606846976)), (213219/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192670987610117/144115188075855872), (-629483505873/144115188075855872)), (373179/144115188075855872), by norm_num⟩
  | 4 => ⟨((744389356262877/18014398509481984), (-942359143619/36028797018963968)), (279929/18014398509481984), by norm_num⟩
  | 3 => ⟨((371423687844571/2251799813685248), (-1174690480799/9007199254740992)), (349991/4503599627370496), by norm_num⟩
  | 2 => ⟨((69401669652329/140737488355328), (-2339634560137/4503599627370496)), (1400449/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205539459983073/2251799813685248), (-3485186843467/2251799813685248)), (525477/562949953421312), by norm_num⟩
  | 0 => ⟨((2159913388857417/2251799813685248), (-6873917351691/2251799813685248)), (2104439/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159913388857417/2251799813685248), (-6873917351691/2251799813685248)), (8027797703269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((517938869196241/562949953421312), (-6593421862629/1125899906842624)), (1012495/281474976710656), by norm_num⟩
  | 2 => ⟨((1906029495453625/2251799813685248), (-6066239890259/562949953421312)), (14999513/2251799813685248), by norm_num⟩
  | 3 => ⟨((1613091726538541/2251799813685248), (-41078010885553/2251799813685248)), (12857927/1125899906842624), by norm_num⟩
  | 4 => ⟨((1154799596058699/2251799813685248), (-29426505455519/1125899906842624)), (37781679/2251799813685248), by norm_num⟩
  | 5 => ⟨((590682360874357/2251799813685248), (-120727309441735/4503599627370496)), (20363193/1125899906842624), by norm_num⟩
  | 6 => ⟨((613308303053451/9007199254740992), (-253349313663353/18014398509481984)), (188398647/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1057560739/16777216)), (1/8388608), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-536384671/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((535795886288447/18014398509481984), (-539884404741461/9007199254740992)), (82195191/9007199254740992), by norm_num⟩
  | 1 => ⟨((-400539613/4294967296), (807192053/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((156986205/1073741824), (-632736503/2147483648)), (99/2147483648), by norm_num⟩
  | 3 => ⟨((-82038223/536870912), (1322627763/4294967296)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((514460747/4294967296), (-1036772925/4294967296)), (83/2147483648), by norm_num⟩
  | 5 => ⟨((-645235479/8589934592), (325079551/2147483648)), (211/8589934592), by norm_num⟩
  | 6 => ⟨((674377371/17179869184), (-84940421/1073741824)), (223/17179869184), by norm_num⟩
  | 7 => ⟨((-302072335/17179869184), (152188685/4294967296)), (101/17179869184), by norm_num⟩
  | 8 => ⟨((236786515/34359738368), (-954373483/68719476736)), (5/2147483648), by norm_num⟩
  | 9 => ⟨((-659949109/274877906944), (41561563/8589934592)), (225/274877906944), by norm_num⟩
  | 10 => ⟨((413853323/549755813888), (-417011329/274877906944)), (143/549755813888), by norm_num⟩
  | 11 => ⟨((-117966791/549755813888), (237733929/549755813888)), (165/2199023255552), by norm_num⟩
  | 12 => ⟨((493178921/8796093022208), (-993884479/8796093022208)), (87/4398046511104), by norm_num⟩
  | 13 => ⟨((-237901485/17592186044416), (958867395/35184372088832)), (85/17592186044416), by norm_num⟩
  | 14 => ⟨((426250703/140737488355328), (-214751655/35184372088832)), (77/70368744177664), by norm_num⟩
  | 15 => ⟨((-89100441/140737488355328), (718242743/562949953421312)), (131/562949953421312), by norm_num⟩
  | 16 => ⟨((558747835/4503599627370496), (-1126022983/4503599627370496)), (207/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1446136637985/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55556163278875/19807040628566084398385987584), (-427412205261/158456325028528675187087900672)), (92369/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888649053243335/39614081257132168796771975168), (-480726520257/9903520314283042199192993792)), (51963/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888356064549897/2475880078570760549798248448), (-2042524277237/2475880078570760549798248448)), (55217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770022581509289/154742504910672534362390528), (-1020945360283/77371252455336267181195264)), (6903/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548458610213107/9671406556917033397649408), (-956799829629/4835703278458516698824704)), (12945/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257831004381187/604462909807314587353088), (-209215888275/75557863725914323419136)), (90631/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943118174299871/37778931862957161709568), (-21238641083/590295810358705651712)), (73651/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296373146344839/4722366482869645213696), (-509451810921/1180591620717411303424)), (110501/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619845197914723/590295810358705651712), (-700048724507/147573952589676412928)), (151979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910736052126049/36893488147419103232), (-109298768309/2305843009213693952)), (95017/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820405606786505/9223372036854775808), (-3931069822669/9223372036854775808)), (13367/576460752303423488), by norm_num⟩
  | 6 => ⟨((795828016603953/576460752303423488), (-1963233765361/576460752303423488)), (213975/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149068040314521/18014398509481984), (-53601380987/2251799813685248)), (187345/144115188075855872), by norm_num⟩
  | 4 => ⟨((46518345469017/1125899906842624), (-5135408319645/36028797018963968)), (70313/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485452289342917/9007199254740992), (-3200615746631/4503599627370496)), (43997/1125899906842624), by norm_num⟩
  | 2 => ⟨((17346561662181/35184372088832), (-12748530109531/4503599627370496)), (705189/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102388914536533/1125899906842624), (-2373562498389/281474976710656)), (1060889/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079153016473657/1125899906842624), (-37443029933743/2251799813685248)), (533569/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079153016473657/1125899906842624), (-37443029933743/2251799813685248)), (2035404207469749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1034035735118211/1125899906842624), (-8972102771601/281474976710656)), (2081151/1125899906842624), by norm_num⟩
  | 2 => ⟨((1897045939804713/2251799813685248), (-32960211928627/562949953421312)), (7910735/2251799813685248), by norm_num⟩
  | 3 => ⟨((795230834205955/1125899906842624), (-222140656853415/2251799813685248)), (3563813/562949953421312), by norm_num⟩
  | 4 => ⟨((550719880201351/1125899906842624), (-39224867767329/281474976710656)), (22949735/2251799813685248), by norm_num⟩
  | 5 => ⟨((990052279899911/4503599627370496), (-306981668213343/2251799813685248)), (28847461/2251799813685248), by norm_num⟩
  | 6 => ⟨((535795886288447/18014398509481984), (-539884404741461/9007199254740992)), (82195191/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-536384671/8388608)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1087330571/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-460288564614625/18014398509481984), (-533447072074317/9007199254740992)), (103498169/4503599627370496), by norm_num⟩
  | 1 => ⟨((1362359/16777216), (808393245/4294967296)), (315/4294967296), by norm_num⟩
  | 2 => ⟨((-277097615/2147483648), (-40142457/134217728)), (503/4294967296), by norm_num⟩
  | 3 => ⟨((9173241/67108864), (680399409/2147483648)), (535/4294967296), by norm_num⟩
  | 4 => ⟨((-466448859/4294967296), (-540586487/2147483648)), (427/4294967296), by norm_num⟩
  | 5 => ⟨((592959833/8589934592), (343602591/2147483648)), (545/8589934592), by norm_num⟩
  | 6 => ⟨((-157038189/4294967296), (-727991687/8589934592)), (579/17179869184), by norm_num⟩
  | 7 => ⟨((570372363/34359738368), (1322055297/34359738368)), (33/2147483648), by norm_num⟩
  | 8 => ⟨((-226584259/34359738368), (-1050390725/68719476736)), (421/68719476736), by norm_num⟩
  | 9 => ⟨((640086197/274877906944), (741821837/137438953472)), (597/274877906944), by norm_num⟩
  | 10 => ⟨((-203422839/274877906944), (-235754973/137438953472)), (381/549755813888), by norm_num⟩
  | 11 => ⟨((58771703/274877906944), (544903269/1099511627776)), (221/1099511627776), by norm_num⟩
  | 12 => ⟨((-498079029/8796093022208), (-1154487947/8796093022208)), (235/4398046511104), by norm_num⟩
  | 13 => ⟨((487052913/35184372088832), (35279085/1099511627776)), (231/17592186044416), by norm_num⟩
  | 14 => ⟨((-27640721/8796093022208), (-1025086457/140737488355328)), (421/140737488355328), by norm_num⟩
  | 15 => ⟨((374799783/562949953421312), (868741317/562949953421312)), (359/562949953421312), by norm_num⟩
  | 16 => ⟨((-595566943/4503599627370496), (-1380453335/4503599627370496)), (143/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-2576695280263/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444434322071419/158456325028528675187087900672), (-3046030907525/633825300114114700748351602688)), (23125/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472145363462443/9903520314283042199192993792), (-3425968373833/39614081257132168796771975168)), (52041/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888284009195005/2475880078570760549798248448), (-3639073196013/2475880078570760549798248448)), (221219/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769950266608053/154742504910672534362390528), (-3637928166113/154742504910672534362390528)), (221269/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548390539468037/9671406556917033397649408), (-1704670741949/4835703278458516698824704)), (103747/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628885583613749/302231454903657293676544), (-745489525421/151115727451828646838272)), (90805/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886138597708515/75557863725914323419136), (-4843403493147/75557863725914323419136)), (295217/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296299382679553/4722366482869645213696), (-3630560009435/4722366482869645213696)), (221501/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619743041904103/590295810358705651712), (-4988783911937/590295810358705651712)), (152353/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910671657340959/36893488147419103232), (-6231129045877/73786976294838206464)), (381097/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56883100518339/288230376151711744), (-875419454725/1152921504606846976)), (429029/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591507770208671/1152921504606846976), (-1748758254185/288230376151711744)), (214699/576460752303423488), by norm_num⟩
  | 5 => ⟨((596206245914709/72057594037927936), (-6111302004685/144115188075855872)), (376139/144115188075855872), by norm_num⟩
  | 4 => ⟨((744192561831437/18014398509481984), (-142941826113/562949953421312)), (565041/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485192586337657/9007199254740992), (-11402724958923/9007199254740992)), (707761/9007199254740992), by norm_num⟩
  | 2 => ⟨((554954690434183/1125899906842624), (-22707834611269/4503599627370496)), (354977/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203912313052841/2251799813685248), (-33818580385393/2251799813685248)), (1070433/1125899906842624), by norm_num⟩
  | 0 => ⟨((134772666550143/140737488355328), (-16667415647517/562949953421312)), (4325961/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((134772666550143/140737488355328), (-16667415647517/562949953421312)), (16502231606490325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062996483972835/2251799813685248), (-127688056825005/2251799813685248)), (533837/140737488355328), by norm_num⟩
  | 2 => ⟨((470695732727015/562949953421312), (-233963970220071/2251799813685248)), (4154787/562949953421312), by norm_num⟩
  | 3 => ⟨((193741268892245/281474976710656), (-195622793332109/1125899906842624)), (7811203/562949953421312), by norm_num⟩
  | 4 => ⟨((998850053478467/2251799813685248), (-33662147029297/140737488355328)), (53869507/2251799813685248), by norm_num⟩
  | 5 => ⟨((628490639818137/4503599627370496), (-477817783354529/2251799813685248)), (147120315/4503599627370496), by norm_num⟩
  | 6 => ⟨((-460288564614625/18014398509481984), (-533447072074317/9007199254740992)), (103498169/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1087330571/16777216)), (1/8388608), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-68831081/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-2071983962011/35184372088832), (-45571122402493/2251799813685248)), (99486239/9007199254740992), by norm_num⟩
  | 1 => ⟨((814142955/4294967296), (279784745/4294967296)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-655156269/2147483648), (-28143511/268435456)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((1405911117/4294967296), (241574579/2147483648)), (271/4294967296), by norm_num⟩
  | 4 => ⟨((-1131363327/4294967296), (-194399643/2147483648)), (55/1073741824), by norm_num⟩
  | 5 => ⟨((1456687225/8589934592), (500598649/8589934592)), (285/8589934592), by norm_num⟩
  | 6 => ⟨((-781482549/8589934592), (-268560815/8589934592)), (77/4294967296), by norm_num⟩
  | 7 => ⟨((1437425877/34359738368), (123494845/8589934592)), (285/34359738368), by norm_num⟩
  | 8 => ⟨((-289180963/17179869184), (-397514571/68719476736)), (231/68719476736), by norm_num⟩
  | 9 => ⟨((413705605/68719476736), (142172227/68719476736)), (167/137438953472), by norm_num⟩
  | 10 => ⟨((-1065333577/549755813888), (-91526949/137438953472)), (217/549755813888), by norm_num⟩
  | 11 => ⟨((155871659/274877906944), (428529285/2199023255552)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1337950707/8796093022208), (-459794185/8796093022208)), (277/8796093022208), by norm_num⟩
  | 13 => ⟨((331284399/8796093022208), (56923861/4398046511104)), (69/8796093022208), by norm_num⟩
  | 14 => ⟨((-304675241/35184372088832), (-418813349/140737488355328)), (1/549755813888), by norm_num⟩
  | 15 => ⟨((130761569/70368744177664), (359495511/562949953421312)), (111/281474976710656), by norm_num⟩
  | 16 => ⟨((-841810507/2251799813685248), (-72323213/562949953421312)), (181/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-1830547809261/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222209750146585/79228162514264337593543950336), (-540962379893/79228162514264337593543950336)), (92627/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888514495107755/39614081257132168796771975168), (-2433736911225/19807040628566084398385987584)), (104233/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888212512425293/2475880078570760549798248448), (-161569506145/77371252455336267181195264)), (110779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769878373070389/154742504910672534362390528), (-2584287261047/77371252455336267181195264)), (110815/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96770169880283/604462909807314587353088), (-2421893164617/4835703278458516698824704)), (103927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257711402745731/604462909807314587353088), (-4236561307779/604462909807314587353088)), (45487/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117877543273323/4722366482869645213696), (-3440564405035/37778931862957161709568)), (2311/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1296225265024985/4722366482869645213696), (-322373430383/295147905179352825856)), (55495/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50613750398143/18446744073709551616), (-7087551132261/590295810358705651712)), (152713/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910606427534619/36893488147419103232), (-553277892541/4611686018427387904)), (191043/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820110153677015/9223372036854775808), (-310918546289/288230376151711744)), (215133/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795677922301663/576460752303423488), (-9937392183101/1152921504606846976)), (53849/288230376151711744), by norm_num⟩
  | 5 => ⟨((596138173077853/72057594037927936), (-8681729669723/144115188075855872)), (94383/72057594037927936), by norm_num⟩
  | 4 => ⟨((744087253989159/18014398509481984), (-12995649949189/36028797018963968)), (70935/9007199254740992), by norm_num⟩
  | 3 => ⟨((92807386023407/562949953421312), (-2024685302993/1125899906842624)), (2779/70368744177664), by norm_num⟩
  | 2 => ⟨((1109618369458003/2251799813685248), (-32254016655335/4503599627370496)), (714539/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101478516232779/1125899906842624), (-12007418995915/562949953421312)), (1079621/2251799813685248), by norm_num⟩
  | 0 => ⟨((538531915392925/562949953421312), (-94660084963217/2251799813685248)), (2190641/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538531915392925/562949953421312), (-94660084963217/2251799813685248)), (8356632241255950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257089097269909/281474976710656), (-22638547421793/281474976710656)), (4375423/2251799813685248), by norm_num⟩
  | 2 => ⟨((1863961077381417/2251799813685248), (-10338616576481/70368744177664)), (2174131/562949953421312), by norm_num⟩
  | 3 => ⟨((747157584124965/1125899906842624), (-136927119545269/562949953421312)), (8476377/1125899906842624), by norm_num⟩
  | 4 => ⟨((858421442813289/2251799813685248), (-726928816452481/2251799813685248)), (30746895/2251799813685248), by norm_num⟩
  | 5 => ⟨((185151333636075/4503599627370496), (-138558338900573/562949953421312)), (43293901/2251799813685248), by norm_num⟩
  | 6 => ⟨((-2071983962011/35184372088832), (-45571122402493/2251799813685248)), (99486239/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-68831081/1048576)), (1/16777216), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1114716163/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-483716466244231/9007199254740992), (15311932101661/562949953421312)), (98203607/4503599627370496), by norm_num⟩
  | 1 => ⟨((751492951/4294967296), (-190306675/2147483648)), (307/4294967296), by norm_num⟩
  | 2 => ⟨((-1224218291/4294967296), (620037519/4294967296)), (251/2147483648), by norm_num⟩
  | 3 => ⟨((1329540459/4294967296), (-336690349/2147483648)), (547/4294967296), by norm_num⟩
  | 4 => ⟨((-135367849/536870912), (274242415/2147483648)), (447/4294967296), by norm_num⟩
  | 5 => ⟨((1411332865/8589934592), (-357403305/4294967296)), (585/8589934592), by norm_num⟩
  | 6 => ⟨((-383188227/4294967296), (194075745/4294967296)), (319/8589934592), by norm_num⟩
  | 7 => ⟨((713408135/17179869184), (-361324293/17179869184)), (149/8589934592), by norm_num⟩
  | 8 => ⟨((-36318009/2147483648), (294307357/34359738368)), (61/8589934592), by norm_num⟩
  | 9 => ⟨((841440565/137438953472), (-26635605/8589934592)), (355/137438953472), by norm_num⟩
  | 10 => ⟨((-1096597837/549755813888), (34712549/34359738368)), (465/549755813888), by norm_num⟩
  | 11 => ⟨((1299207861/2199023255552), (-658017953/2199023255552)), (553/2199023255552), by norm_num⟩
  | 12 => ⟨((-1410981545/8796093022208), (11166073/137438953472)), (603/8796093022208), by norm_num⟩
  | 13 => ⟨((707248321/17592186044416), (-716408985/35184372088832)), (607/35184372088832), by norm_num⟩
  | 14 => ⟨((-658366659/70368744177664), (666894181/140737488355328)), (567/140737488355328), by norm_num⟩
  | 15 => ⟨((286002951/140737488355328), (-579414833/562949953421312)), (495/562949953421312), by norm_num⟩
  | 16 => ⟨((-931825225/2251799813685248), (471947365/2251799813685248)), (405/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (3481591056165/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888813438071043/316912650057057350374175801344), (2057640346111/316912650057057350374175801344)), (92605/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118028565415489/2475880078570760549798248448), (1157137856211/9903520314283042199192993792)), (208415/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888151561653379/2475880078570760549798248448), (4916424505971/2475880078570760549798248448)), (110751/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769817521459685/154742504910672534362390528), (4914837154481/154742504910672534362390528)), (221569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548265774985469/9671406556917033397649408), (4605973780935/9671406556917033397649408)), (207793/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628830841369095/302231454903657293676544), (2014270789765/302231454903657293676544)), (45473/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((58936252951401/2361183241434822606848), (6543221010693/75557863725914323419136)), (295709/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648082494426709/2361183241434822606848), (2452326400275/2361183241434822606848)), (221901/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619557412625447/590295810358705651712), (6739410075687/590295810358705651712)), (152653/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455277505946773/18446744073709551616), (8417535297937/73786976294838206464)), (190961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819995043494953/9223372036854775808), (9460483661583/9223372036854775808)), (430061/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795620725899287/576460752303423488), (590558684417/72057594037927936)), (13455/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192177057597777/144115188075855872), (8254847151005/144115188075855872)), (188651/72057594037927936), by norm_num⟩
  | 4 => ⟨((744013590340889/18014398509481984), (12356355279007/36028797018963968)), (567077/36028797018963968), by norm_num⟩
  | 3 => ⟨((185592102034217/1125899906842624), (15400167224759/9007199254740992)), (710817/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109441186576957/2251799813685248), (15332402174519/2251799813685248)), (178445/562949953421312), by norm_num⟩
  | 1 => ⟨((550611555280661/562949953421312), (45659432573023/2251799813685248)), (539051/562949953421312), by norm_num⟩
  | 0 => ⟨((2153188098279131/2251799813685248), (1405844888747/35184372088832)), (2186073/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153188098279131/2251799813685248), (1405844888747/35184372088832)), (8339206699851607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1027649888025799/1125899906842624), (86033892400695/1125899906842624)), (8710751/2251799813685248), by norm_num⟩
  | 2 => ⟨((931399368047379/1125899906842624), (157052539670129/1125899906842624)), (8616239/1125899906842624), by norm_num⟩
  | 3 => ⟨((748591662065063/1125899906842624), (16240190991889/70368744177664)), (33318635/2251799813685248), by norm_num⟩
  | 4 => ⟨((875514883399399/2251799813685248), (691060879880311/2251799813685248)), (29842501/1125899906842624), by norm_num⟩
  | 5 => ⟨((16040567282933/281474976710656), (268689109037677/1125899906842624)), (166091283/4503599627370496), by norm_num⟩
  | 6 => ⟨((-483716466244231/9007199254740992), (15311932101661/562949953421312)), (98203607/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1114716163/16777216)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-563814267/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-342477230719471/18014398509481984), (992268259515357/18014398509481984)), (23123451/2251799813685248), by norm_num⟩
  | 1 => ⟨((538229505/8589934592), (-194928307/1073741824)), (293/8589934592), by norm_num⟩
  | 2 => ⟨((-443479161/4294967296), (1284903801/4294967296)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((60901457/536870912), (-1411611105/4294967296)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((-200721267/2147483648), (290777495/1073741824)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((529235641/8589934592), (-383342075/2147483648)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((-290712389/8589934592), (842288629/8589934592)), (41/2147483648), by norm_num⟩
  | 7 => ⟨((547508919/34359738368), (-99144497/2147483648)), (311/34359738368), by norm_num⟩
  | 8 => ⟨((-112781255/17179869184), (1307056353/68719476736)), (129/34359738368), by norm_num⟩
  | 9 => ⟨((82601915/34359738368), (-957298781/137438953472)), (191/137438953472), by norm_num⟩
  | 10 => ⟨((-435587899/549755813888), (631020123/274877906944)), (127/274877906944), by norm_num⟩
  | 11 => ⟨((522046057/2199023255552), (-756268867/1099511627776)), (307/2199023255552), by norm_num⟩
  | 12 => ⟨((-286763107/4398046511104), (830846271/4398046511104)), (85/2199023255552), by norm_num⟩
  | 13 => ⟨((145403757/8796093022208), (-842564237/17592186044416)), (87/8796093022208), by norm_num⟩
  | 14 => ⟨((-68461009/17592186044416), (793415507/70368744177664)), (165/70368744177664), by norm_num⟩
  | 15 => ⟨((481357477/562949953421312), (-697324821/281474976710656)), (73/140737488355328), by norm_num⟩
  | 16 => ⟨((-198309465/1125899906842624), (574567213/1125899906842624)), (243/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (2479052559837/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777581238587417/633825300114114700748351602688), (2930111044101/633825300114114700748351602688)), (92489/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944202980808187/19807040628566084398385987584), (3295563433135/39614081257132168796771975168)), (104069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29501525455613/38685626227668133590597632), (3500520587179/2475880078570760549798248448)), (110595/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884881988524133/77371252455336267181195264), (874844643073/38685626227668133590597632)), (110619/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48381749659201/302231454903657293676544), (409931808769/1208925819614629174706176)), (103731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2456286194711/1180591620717411303424), (2868310225567/604462909807314587353088)), (45395/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885890744940689/75557863725914323419136), (1164682968323/18889465931478580854784)), (147583/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648056825241735/2361183241434822606848), (1746030882783/2361183241434822606848)), (110729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809743957844277/295147905179352825856), (1199589459465/147573952589676412928)), (152321/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910512394957285/36893488147419103232), (1498277545309/18446744073709551616)), (190505/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909950701158551/4611686018427387904), (3367801816679/4611686018427387904)), (53615/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795575306377397/576460752303423488), (840913193433/144115188075855872)), (214637/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596050358437261/72057594037927936), (1469267193407/36028797018963968)), (23501/18014398509481984), by norm_num⟩
  | 4 => ⟨((371979733528985/9007199254740992), (8796985384211/36028797018963968)), (70603/9007199254740992), by norm_num⟩
  | 3 => ⟨((371153105193679/2251799813685248), (5481858325983/4503599627370496)), (176859/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218666120041585/4503599627370496), (10915075881873/2251799813685248)), (177387/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202202487852987/2251799813685248), (16251472406109/1125899906842624)), (1069621/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076509523790623/1125899906842624), (4002641818185/140737488355328)), (2160549/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076509523790623/1125899906842624), (4002641818185/140737488355328)), (8241840371138762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2056750151088121/2251799813685248), (122465793242519/2251799813685248)), (4254437/2251799813685248), by norm_num⟩
  | 2 => ⟨((935967595313889/1125899906842624), (223715747042765/2251799813685248)), (4117301/1125899906842624), by norm_num⟩
  | 3 => ⟨((191740657930803/281474976710656), (371952583921361/2251799813685248)), (3831791/562949953421312), by norm_num⟩
  | 4 => ⟨((245867547338619/562949953421312), (506747946077325/2251799813685248)), (25945205/2251799813685248), by norm_num⟩
  | 5 => ⟨((315489915301433/2251799813685248), (885285619893599/4503599627370496)), (68681089/4503599627370496), by norm_num⟩
  | 6 => ⟨((-342477230719471/18014398509481984), (992268259515357/18014398509481984)), (23123451/2251799813685248), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-563814267/8388608)), (1/16777216), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile014Terms3

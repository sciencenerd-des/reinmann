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
namespace Reinmann.XiBand97.Tile041Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35053/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35053/1280))
  have he : value ((69/80), (35053/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-79616043/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1389293595157/17592186044416), (-52043157305125/1125899906842624)), (39896067/2251799813685248), by norm_num⟩
  | 1 => ⟨((-940414979/4294967296), (550438961/4294967296)), (213/4294967296), by norm_num⟩
  | 2 => ⟨((1303691983/4294967296), (-190767607/1073741824)), (149/2147483648), by norm_num⟩
  | 3 => ⟨((-602433615/2147483648), (705226821/4294967296)), (277/4294967296), by norm_num⟩
  | 4 => ⟨((835150323/4294967296), (-488825983/4294967296)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((-926211347/8589934592), (542125363/8589934592)), (217/8589934592), by norm_num⟩
  | 6 => ⟨((856001045/17179869184), (-501030223/17179869184)), (203/17179869184), by norm_num⟩
  | 7 => ⟨((-169524203/8589934592), (396900213/34359738368)), (163/34359738368), by norm_num⟩
  | 8 => ⟨((940041787/137438953472), (-550220527/137438953472)), (57/34359738368), by norm_num⟩
  | 9 => ⟨((-144797181/68719476736), (678015657/549755813888)), (283/549755813888), by norm_num⟩
  | 10 => ⟨((1284681699/2199023255552), (-375971713/1099511627776)), (79/549755813888), by norm_num⟩
  | 11 => ⟨((-647617089/4398046511104), (379059975/4398046511104)), (321/8796093022208), by norm_num⟩
  | 12 => ⟨((598525279/17592186044416), (-87581451/4398046511104)), (299/35184372088832), by norm_num⟩
  | 13 => ⟨((-1021208885/140737488355328), (597728845/140737488355328)), (257/140737488355328), by norm_num⟩
  | 14 => ⟨((808969211/562949953421312), (-473501787/562949953421312)), (205/562949953421312), by norm_num⟩
  | 15 => ⟨((-598117043/2251799813685248), (350086857/2251799813685248)), (305/4503599627370496), by norm_num⟩
  | 16 => ⟨((207291571/4503599627370496), (-121330859/4503599627370496)), (213/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-689800209889/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778280580812421/633825300114114700748351602688), (-815915954129/633825300114114700748351602688)), (184561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472298193790587/9903520314283042199192993792), (-458857593781/19807040628566084398385987584)), (207641/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472233427031125/618970019642690137449562112), (-974834623431/2475880078570760549798248448)), (220631/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770600156455281/154742504910672534362390528), (-974567257809/154742504910672534362390528)), (220645/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387250003446527/2417851639229258349412352), (-913372830355/9671406556917033397649408)), (206869/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258304659545009/604462909807314587353088), (-798917367659/604462909807314587353088)), (181025/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887005901385925/75557863725914323419136), (-1297708731137/75557863725914323419136)), (294191/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296950191136189/4722366482869645213696), (-486408149979/2361183241434822606848)), (55167/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620638439736825/590295810358705651712), (-1336866841029/590295810358705651712)), (9483/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1822463364217031/73786976294838206464), (-417487748441/18446744073709551616)), (189689/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821520372051931/9223372036854775808), (-469284724927/2305843009213693952)), (426879/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796385147666553/576460752303423488), (-1875195885037/1152921504606846976)), (426979/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193518735300357/144115188075855872), (-204826647535/18014398509481984)), (46715/18014398509481984), by norm_num⟩
  | 4 => ⟨((186255942460571/4503599627370496), (-613390001087/9007199254740992)), (140201/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487275906795175/9007199254740992), (-3059335403161/9007199254740992)), (87675/1125899906842624), by norm_num⟩
  | 2 => ⟨((2224001150511531/4503599627370496), (-6095886832789/4503599627370496)), (1403989/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210224731340599/2251799813685248), (-1135884899051/281474976710656)), (2108979/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084569827280541/1125899906842624), (-17948403115011/2251799813685248)), (1057511/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084569827280541/1125899906842624), (-17948403115011/2251799813685248)), (4034084322215843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1044685381715869/1125899906842624), (-34579088865899/2251799813685248)), (8216965/2251799813685248), by norm_num⟩
  | 2 => ⟨((1938127202592689/2251799813685248), (-64169591686995/2251799813685248)), (15500865/2251799813685248), by norm_num⟩
  | 3 => ⟨((833160055820345/1125899906842624), (-55230855989943/1125899906842624)), (13783345/1125899906842624), by norm_num⟩
  | 4 => ⟨((1227649504118451/2251799813685248), (-163482180893433/2251799813685248)), (43502975/2251799813685248), by norm_num⟩
  | 5 => ⟨((164357070341637/562949953421312), (-356512718557457/4503599627370496)), (53751109/2251799813685248), by norm_num⟩
  | 6 => ⟨((1389293595157/17592186044416), (-52043157305125/1125899906842624)), (39896067/2251799813685248), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-79616043/1048576)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1301710469/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-907680035637801/18014398509481984), (-637097804538353/9007199254740992)), (568345951/18014398509481984), by norm_num⟩
  | 1 => ⟨((306564711/2147483648), (215176821/1073741824)), (193/2147483648), by norm_num⟩
  | 2 => ⟨((-434281615/2147483648), (-1219283681/4294967296)), (549/4294967296), by norm_num⟩
  | 3 => ⟨((410137489/2147483648), (287874233/1073741824)), (521/4294967296), by norm_num⟩
  | 4 => ⟨((-581003503/4294967296), (-407804559/2147483648)), (371/4294967296), by norm_num⟩
  | 5 => ⟨((658442751/8589934592), (924317855/8589934592)), (211/4294967296), by norm_num⟩
  | 6 => ⟨((-621836263/17179869184), (-436464947/8589934592)), (25/1073741824), by norm_num⟩
  | 7 => ⟨((251684971/17179869184), (706627607/34359738368)), (163/17179869184), by norm_num⟩
  | 8 => ⟨((-356538609/68719476736), (-1001013383/137438953472)), (29/8589934592), by norm_num⟩
  | 9 => ⟨((448955531/274877906944), (315120497/137438953472)), (147/137438953472), by norm_num⟩
  | 10 => ⟨((-508794721/1099511627776), (-357121439/549755813888)), (335/1099511627776), by norm_num⟩
  | 11 => ⟨((524190543/4398046511104), (735855437/4398046511104)), (347/4398046511104), by norm_num⟩
  | 12 => ⟨((-61880985/2199023255552), (-173736287/4398046511104)), (165/8796093022208), by norm_num⟩
  | 13 => ⟨((215780963/35184372088832), (605823959/70368744177664)), (577/140737488355328), by norm_num⟩
  | 14 => ⟨((-698689719/562949953421312), (-245204075/140737488355328)), (469/562949953421312), by norm_num⟩
  | 15 => ⟨((527876543/2251799813685248), (741029821/2251799813685248)), (89/562949953421312), by norm_num⟩
  | 16 => ⟨((-747793433/18014398509481984), (-1049747789/18014398509481984)), (253/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-2852415249435/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778194276546569/633825300114114700748351602688), (-3373629252231/633825300114114700748351602688)), (23133/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236136923007019/4951760157141521099596496896), (-1897258865211/19807040628566084398385987584)), (208241/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888829832542849/2475880078570760549798248448), (-4030669115579/2475880078570760549798248448)), (221305/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770495834119107/154742504910672534362390528), (-4029537703187/154742504910672534362390528)), (13835/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774450868643203/4835703278458516698824704), (-1888244900811/4835703278458516698824704)), (207585/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258218193711451/604462909807314587353088), (-825806788229/151115727451828646838272)), (2839/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((235858063341039/9444732965739290427392), (-2682746121993/37778931862957161709568)), (147683/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40526355290673/147573952589676412928), (-2011074788935/2361183241434822606848)), (110811/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810245150307307/295147905179352825856), (-5527256541201/590295810358705651712)), (38111/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822276304537073/73786976294838206464), (-3452137286667/36893488147419103232)), (381347/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821307341630477/9223372036854775808), (-7760718459919/9223372036854775808)), (214671/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592554036544075/1152921504606846976), (-7752486724505/1152921504606846976)), (429749/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149165735816921/18014398509481984), (-1693543463225/36028797018963968)), (188245/72057594037927936), by norm_num⟩
  | 4 => ⟨((744875522908437/18014398509481984), (-5071389193541/18014398509481984)), (565655/36028797018963968), by norm_num⟩
  | 3 => ⟨((743446353460617/4503599627370496), (-12646177531193/9007199254740992)), (354341/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223197217435135/4503599627370496), (-787364485089/140737488355328)), (11111/35184372088832), by norm_num⟩
  | 1 => ⟨((1104462872873383/1125899906842624), (-18776223885945/1125899906842624)), (1072731/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166173802191273/2251799813685248), (-74144789263815/2251799813685248)), (2169859/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166173802191273/2251799813685248), (-74144789263815/2251799813685248)), (8277355198386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2081362411987451/2251799813685248), (-142650780141435/2251799813685248)), (8635183/2251799813685248), by norm_num⟩
  | 2 => ⟨((478697109169619/562949953421312), (-263707253213735/2251799813685248)), (17057255/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597332595899589/2251799813685248), (-448480007905785/2251799813685248)), (16501981/1125899906842624), by norm_num⟩
  | 4 => ⟨((260939836897139/562949953421312), (-636265915720827/2251799813685248)), (29984869/1125899906842624), by norm_num⟩
  | 5 => ⟨((608046289026043/4503599627370496), (-1179693670901837/4503599627370496)), (178969155/4503599627370496), by norm_num⟩
  | 6 => ⟨((-907680035637801/18014398509481984), (-637097804538353/9007199254740992)), (568345951/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1301710469/16777216)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1327971713/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1217639416096379/18014398509481984), (428664073755171/9007199254740992)), (543432607/18014398509481984), by norm_num⟩
  | 1 => ⟨((419548819/2147483648), (-590800539/4294967296)), (47/536870912), by norm_num⟩
  | 2 => ⟨((-606326029/2147483648), (213454149/1073741824)), (273/2147483648), by norm_num⟩
  | 3 => ⟨((292084605/1073741824), (-51413487/268435456)), (33/268435456), by norm_num⟩
  | 4 => ⟨((-844233093/4294967296), (594416363/4294967296)), (3/33554432), by norm_num⟩
  | 5 => ⟨((244014749/2147483648), (-687233707/8589934592)), (223/4294967296), by norm_num⟩
  | 6 => ⟨((-940391119/17179869184), (662120299/17179869184)), (27/1073741824), by norm_num⟩
  | 7 => ⟨((388297133/17179869184), (-273396259/17179869184)), (179/17179869184), by norm_num⟩
  | 8 => ⟨((-1122323067/137438953472), (395108413/68719476736)), (519/137438953472), by norm_num⟩
  | 9 => ⟨((720873533/274877906944), (-63445011/34359738368)), (335/274877906944), by norm_num⟩
  | 10 => ⟨((-104179625/137438953472), (293407469/549755813888)), (195/549755813888), by norm_num⟩
  | 11 => ⟨((218994797/1099511627776), (-308384241/2199023255552)), (103/1099511627776), by norm_num⟩
  | 12 => ⟨((-421984251/8796093022208), (594230067/17592186044416)), (399/17592186044416), by norm_num⟩
  | 13 => ⟨((750579299/70368744177664), (-33029727/4398046511104)), (357/70368744177664), by norm_num⟩
  | 14 => ⟨((-309921887/140737488355328), (109106503/70368744177664)), (37/35184372088832), by norm_num⟩
  | 15 => ⟨((955508767/2251799813685248), (-672764491/2251799813685248)), (459/2251799813685248), by norm_num⟩
  | 16 => ⟨((-690443889/9007199254740992), (486134871/9007199254740992)), (333/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (823291845601/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778116296944793/633825300114114700748351602688), (30426575945/4951760157141521099596496896)), (185167/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944503782014149/19807040628566084398385987584), (4380463258577/39614081257132168796771975168)), (104181/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888736397794123/2475880078570760549798248448), (2326528481953/1237940039285380274899124224)), (110721/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885201128910579/77371252455336267181195264), (581465481827/19342813113834066795298816)), (221507/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548813859245063/9671406556917033397649408), (4359575042615/9671406556917033397649408)), (207731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258141150314023/604462909807314587353088), (3813212492959/604462909807314587353088)), (181833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943369515034539/37778931862957161709568), (3096908387411/37778931862957161709568)), (147803/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296749016130965/4722366482869645213696), (1160760399857/1180591620717411303424)), (221817/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202545020797603/73786976294838206464), (6380412204815/590295810358705651712)), (76295/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822113039856623/73786976294838206464), (7969863065959/73786976294838206464)), (381749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821122849845239/9223372036854775808), (8958328740475/9223372036854775808)), (107461/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592368523533501/1152921504606846976), (2237156639661/288230376151711744)), (430315/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149145302159131/18014398509481984), (3909571337253/72057594037927936)), (377057/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489503559903689/36028797018963968), (11706926359529/36028797018963968)), (566647/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486579375611941/9007199254740992), (14595582381781/9007199254740992)), (710171/9007199254740992), by norm_num⟩
  | 2 => ⟨((555639677832117/1125899906842624), (29077149364273/4503599627370496)), (1425937/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103969325445039/1125899906842624), (21665712571783/1125899906842624)), (269117/281474976710656), by norm_num⟩
  | 0 => ⟨((2164083900598375/2251799813685248), (85530092455171/2251799813685248)), (4362225/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164083900598375/2251799813685248), (85530092455171/2251799813685248)), (16640567788130950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((259567019662215/281474976710656), (164396759404651/2251799813685248)), (4357991/1125899906842624), by norm_num⟩
  | 2 => ⟨((475727914624139/562949953421312), (303202631931693/2251799813685248)), (17347841/2251799813685248), by norm_num⟩
  | 3 => ⟨((783626706642295/1125899906842624), (128112592354603/562949953421312)), (16995881/1125899906842624), by norm_num⟩
  | 4 => ⟨((974188676543589/2251799813685248), (178332813096639/562949953421312)), (31393909/1125899906842624), by norm_num⟩
  | 5 => ⟨((195489003595729/2251799813685248), (154303065591419/562949953421312)), (94107563/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1217639416096379/18014398509481984), (428664073755171/9007199254740992)), (543432607/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1327971713/16777216)), (1/8388608), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-676406359/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((710307859790603/18014398509481984), (1231113497390943/18014398509481984)), (11727537/562949953421312), by norm_num⟩
  | 1 => ⟨((-31165155/268435456), (-864252703/4294967296)), (265/4294967296), by norm_num⟩
  | 2 => ⟨((734111177/4294967296), (1272369673/4294967296)), (49/536870912), by norm_num⟩
  | 3 => ⟨((-180128797/1073741824), (-624402477/2147483648)), (387/4294967296), by norm_num⟩
  | 4 => ⟨((530378251/4294967296), (114907187/536870912)), (143/2147483648), by norm_num⟩
  | 5 => ⟨((-312333279/4294967296), (-1082679041/8589934592)), (339/8589934592), by norm_num⟩
  | 6 => ⟨((613097521/17179869184), (1062627457/17179869184)), (335/17179869184), by norm_num⟩
  | 7 => ⟨((-515779497/34359738368), (-893954773/34359738368)), (71/8589934592), by norm_num⟩
  | 8 => ⟨((189835157/34359738368), (164512205/17179869184)), (421/137438953472), by norm_num⟩
  | 9 => ⟨((-496851587/274877906944), (-861148709/274877906944)), (277/274877906944), by norm_num⟩
  | 10 => ⟨((73147459/137438953472), (507119965/549755813888)), (41/137438953472), by norm_num⟩
  | 11 => ⟨((-626554849/4398046511104), (-1085951849/4398046511104)), (353/4398046511104), by norm_num⟩
  | 12 => ⟨((76868855/2199023255552), (1065839651/17592186044416)), (87/4398046511104), by norm_num⟩
  | 13 => ⟨((-557133915/70368744177664), (-120703839/8796093022208)), (317/70368744177664), by norm_num⟩
  | 14 => ⟨((234349545/140737488355328), (101544311/35184372088832)), (67/70368744177664), by norm_num⟩
  | 15 => ⟨((-736029797/2251799813685248), (-637847525/1125899906842624)), (423/2251799813685248), by norm_num⟩
  | 16 => ⟨((270899353/4503599627370496), (469525779/4503599627370496)), (313/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1364469407417/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889025597946549/316912650057057350374175801344), (1613539496835/633825300114114700748351602688)), (184717/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472233678705617/9903520314283042199192993792), (1814832688139/39614081257132168796771975168)), (51957/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888659511437987/2475880078570760549798248448), (1927760323847/2475880078570760549798248448)), (220841/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442581487826973/38685626227668133590597632), (963599370561/77371252455336267181195264)), (55217/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548742937512001/9671406556917033397649408), (225769044591/1208925819614629174706176)), (51773/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258079708903219/604462909807314587353088), (1579787095023/604462909807314587353088)), (90617/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886640340000543/75557863725914323419136), (2566036644747/75557863725914323419136)), (147279/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648338002838655/2361183241434822606848), (961775147067/2361183241434822606848)), (220965/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405065352870805/147573952589676412928), (2643294700089/590295810358705651712)), (151951/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821992044351143/73786976294838206464), (3301739654783/73786976294838206464)), (47499/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910495045110727/4611686018427387904), (3711189149731/9223372036854775808)), (3341/72057594037927936), by norm_num⟩
  | 6 => ⟨((1592239955559497/1152921504606846976), (3707108361455/1152921504606846976)), (427843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596527311943707/72057594037927936), (3239134649043/144115188075855872)), (46823/18014398509481984), by norm_num⟩
  | 4 => ⟨((186168905877919/4503599627370496), (4849545919919/36028797018963968)), (281159/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486405327281355/9007199254740992), (3022970694009/4503599627370496)), (87959/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111129687183415/2251799813685248), (12044037819613/4503599627370496)), (704837/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207610607695715/2251799813685248), (17946891498089/2251799813685248)), (2120363/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163906066225219/2251799813685248), (35419796108667/2251799813685248)), (4264267/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163906066225219/2251799813685248), (35419796108667/2251799813685248)), (16266887673384856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2078885908525195/2251799813685248), (17018633538869/562949953421312)), (4164897/1125899906842624), by norm_num⟩
  | 2 => ⟨((1917191951179183/2251799813685248), (125694290340693/2251799813685248)), (15883951/2251799813685248), by norm_num⟩
  | 3 => ⟨((812644601176247/1125899906842624), (107016654094119/1125899906842624)), (7205149/562949953421312), by norm_num⟩
  | 4 => ⟨((288186667226587/562949953421312), (308967096122827/2251799813685248)), (47082669/2251799813685248), by norm_num⟩
  | 5 => ⟨((1095447480448639/4503599627370496), (632668656765489/4503599627370496)), (61125671/2251799813685248), by norm_num⟩
  | 6 => ⟨((710307859790603/18014398509481984), (1231113497390943/18014398509481984)), (11727537/562949953421312), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-676406359/8388608)), (1/8388608), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-344094813/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((636996704087019/9007199254740992), (-475448161747389/18014398509481984)), (116060569/9007199254740992), by norm_num⟩
  | 1 => ⟨((-56870925/268435456), (339583255/4294967296)), (21/536870912), by norm_num⟩
  | 2 => ⟨((340740131/1073741824), (-254325129/2147483648)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((-680510805/2147483648), (507926665/4294967296)), (1/16777216), by norm_num⟩
  | 4 => ⟨((1019314091/4294967296), (-95100769/1073741824)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((-76339803/536870912), (455834309/8589934592)), (117/4294967296), by norm_num⟩
  | 6 => ⟨((609849631/8589934592), (-227592925/8589934592)), (59/4294967296), by norm_num⟩
  | 7 => ⟨((-521984635/17179869184), (389604269/34359738368)), (51/8589934592), by norm_num⟩
  | 8 => ⟨((781863109/68719476736), (-583575041/137438953472)), (77/34359738368), by norm_num⟩
  | 9 => ⟨((-1041001133/274877906944), (194248287/137438953472)), (207/274877906944), by norm_num⟩
  | 10 => ⟨((1247424277/1099511627776), (-232766345/549755813888)), (125/549755813888), by norm_num⟩
  | 11 => ⟨((-679445303/2199023255552), (507131383/4398046511104)), (275/4398046511104), by norm_num⟩
  | 12 => ⟨((678478741/8796093022208), (-253204975/8796093022208)), (277/17592186044416), by norm_num⟩
  | 13 => ⟨((-1250794253/70368744177664), (116697587/17592186044416)), (257/70368744177664), by norm_num⟩
  | 14 => ⟨((1070584203/281474976710656), (-6242763/4398046511104)), (111/140737488355328), by norm_num⟩
  | 15 => ⟨((-855248973/1125899906842624), (319174769/1125899906842624)), (179/1125899906842624), by norm_num⟩
  | 16 => ⟨((1281048475/9007199254740992), (-239040539/4503599627370496)), (135/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-232638233261/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777984284258199/633825300114114700748351602688), (-137541944057/158456325028528675187087900672)), (184509/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888859524107673/39614081257132168796771975168), (-618800826939/39614081257132168796771975168)), (51895/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888579733017499/2475880078570760549798248448), (-164325671353/618970019642690137449562112)), (220561/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442561574610239/38685626227668133590597632), (-328553969811/77371252455336267181195264)), (110285/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774334198128087/4835703278458516698824704), (-153957964289/2417851639229258349412352)), (206795/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258014618505751/604462909807314587353088), (-538646130123/604462909807314587353088)), (180955/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886534817633133/75557863725914323419136), (-874912508803/75557863725914323419136)), (147035/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324149270503809/1180591620717411303424), (-163961388611/1180591620717411303424)), (220569/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620153245462793/590295810358705651712), (-450618703281/295147905179352825856)), (75827/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821857367114677/73786976294838206464), (-562861023679/36893488147419103232)), (189587/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820839306287711/9223372036854775808), (-1265304357411/9223372036854775808)), (213313/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398022519947405/288230376151711744), (-631944860409/576460752303423488)), (213347/576460752303423488), by norm_num⟩
  | 5 => ⟨((596462250912997/72057594037927936), (-1104314162379/144115188075855872)), (373433/144115188075855872), by norm_num⟩
  | 4 => ⟨((372289524075057/9007199254740992), (-1653297856295/36028797018963968)), (35019/2251799813685248), by norm_num⟩
  | 3 => ⟨((1486167431819953/9007199254740992), (-2061080795213/9007199254740992)), (700651/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221794157628049/4503599627370496), (-4105584520053/4503599627370496)), (175265/562949953421312), by norm_num⟩
  | 1 => ⟨((275867378444527/281474976710656), (-1529274974909/562949953421312)), (2105247/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162666748938723/2251799813685248), (-12070083282043/2251799813685248)), (2109441/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162666748938723/2251799813685248), (-12070083282043/2251799813685248)), (8046878818992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2076997143187653/2251799813685248), (-11592312785689/1125899906842624)), (8149001/2251799813685248), by norm_num⟩
  | 2 => ⟨((1915525340988283/2251799813685248), (-42769699850733/2251799813685248)), (15200627/2251799813685248), by norm_num⟩
  | 3 => ⟨((1628656358551231/2251799813685248), (-4547831216647/140737488355328)), (13219343/1125899906842624), by norm_num⟩
  | 4 => ⟨((1175604833677703/2251799813685248), (-105257729339455/2251799813685248)), (39953245/2251799813685248), by norm_num⟩
  | 5 => ⟨((1217663779034589/4503599627370496), (-219809051659685/4503599627370496)), (45452191/2251799813685248), by norm_num⟩
  | 6 => ⟨((636996704087019/9007199254740992), (-475448161747389/18014398509481984)), (116060569/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-344094813/4194304)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1398795731/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-159336814676867/18014398509481984), (-161751363893725/2251799813685248)), (437613627/18014398509481984), by norm_num⟩
  | 1 => ⟨((231315855/8589934592), (1878569247/8589934592)), (319/4294967296), by norm_num⟩
  | 2 => ⟨((-88030789/2147483648), (-357459139/1073741824)), (487/4294967296), by norm_num⟩
  | 3 => ⟨((178674475/4294967296), (1451056493/4294967296)), (31/268435456), by norm_num⟩
  | 4 => ⟨((-33998653/1073741824), (-1104443513/4294967296)), (379/4294967296), by norm_num⟩
  | 5 => ⟨((165615459/8589934592), (1345001223/8589934592)), (463/8589934592), by norm_num⟩
  | 6 => ⟨((-168073327/17179869184), (-682481067/8589934592)), (59/2147483648), by norm_num⟩
  | 7 => ⟨((73100431/17179869184), (1187330813/34359738368)), (413/34359738368), by norm_num⟩
  | 8 => ⟨((-111277951/68719476736), (-1807427651/137438953472)), (631/137438953472), by norm_num⟩
  | 9 => ⟨((75286271/137438953472), (1222834231/274877906944)), (429/274877906944), by norm_num⟩
  | 10 => ⟨((-183368593/1099511627776), (-744589251/549755813888)), (131/274877906944), by norm_num⟩
  | 11 => ⟨((101503599/2199023255552), (412167033/1099511627776)), (583/4398046511104), by norm_num⟩
  | 12 => ⟨((-103009995/8796093022208), (-1673135707/17592186044416)), (593/17592186044416), by norm_num⟩
  | 13 => ⟨((96497305/35184372088832), (1567353601/70368744177664)), (279/35184372088832), by norm_num⟩
  | 14 => ⟨((-167878977/281474976710656), (-1363383773/281474976710656)), (61/35184372088832), by norm_num⟩
  | 15 => ⟨((68148175/562949953421312), (1106893997/1125899906842624)), (397/1125899906842624), by norm_num⟩
  | 16 => ⟨((-25934831/1125899906842624), (-1684981805/9007199254740992)), (303/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-551432527437/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444478996025963/158456325028528675187087900672), (-2607991950489/633825300114114700748351602688)), (184913/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888782511809197/39614081257132168796771975168), (-91666293507/1237940039285380274899124224)), (208061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236062209072669/309485009821345068724781056), (-3115818973971/2475880078570760549798248448)), (13819/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((110635248380957/9671406556917033397649408), (-97339998983/4835703278458516698824704)), (221147/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774295468507035/4835703278458516698824704), (-2919202620691/9671406556917033397649408)), (207371/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314486640441587/151115727451828646838272), (-1276652666549/302231454903657293676544)), (181495/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943211850589031/37778931862957161709568), (-4147252692153/75557863725914323419136)), (295015/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648256643257683/2361183241434822606848), (-3108805429793/4722366482869645213696)), (221337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101252330199871/36893488147419103232), (-4271953617989/590295810358705651712)), (76115/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821711300949255/73786976294838206464), (-5335963956637/73786976294838206464)), (380759/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455168363502575/2305843009213693952), (-5997494005411/9223372036854775808)), (214303/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591922322194037/1152921504606846976), (-5990668785539/1152921504606846976)), (214461/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192775576600867/144115188075855872), (-1308541466245/36028797018963968)), (187831/72057594037927936), by norm_num⟩
  | 4 => ⟨((186116306144629/4503599627370496), (-3917966377361/18014398509481984)), (282103/18014398509481984), by norm_num⟩
  | 3 => ⟨((742937726780229/4503599627370496), (-4884081829943/4503599627370496)), (353253/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221188080490301/4503599627370496), (-19456273318695/4503599627370496)), (22137/70368744177664), by norm_num⟩
  | 1 => ⟨((1102987544557727/1125899906842624), (-3623122941135/281474976710656)), (2134571/2251799813685248), by norm_num⟩
  | 0 => ⟨((33758163095527/35184372088832), (-57176501240851/2251799813685248)), (1076749/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((33758163095527/35184372088832), (-57176501240851/2251799813685248)), (4107471468211936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((258936652858185/281474976710656), (-54858834747627/1125899906842624)), (1060443/281474976710656), by norm_num⟩
  | 2 => ⟨((118767390516143/140737488355328), (-50466166531929/562949953421312)), (16435209/2251799813685248), by norm_num⟩
  | 3 => ⟨((1585535293001753/2251799813685248), (-85176095984001/562949953421312)), (15342909/1125899906842624), by norm_num⟩
  | 4 => ⟨((266214016178095/562949953421312), (-479792938899729/2251799813685248)), (52498665/2251799813685248), by norm_num⟩
  | 5 => ⟨((401331045879115/2251799813685248), (-907559220297487/4503599627370496)), (144048351/4503599627370496), by norm_num⟩
  | 6 => ⟨((-159336814676867/18014398509481984), (-161751363893725/2251799813685248)), (437613627/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1398795731/16777216)), (1/8388608), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile041Terms2

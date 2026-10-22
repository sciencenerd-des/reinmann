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
namespace Reinmann.XiBand97.Tile023Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28967/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28967/1280))
  have he : value ((69/80), (28967/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1052686123/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1642197962344069/18014398509481984), (71509375168417/9007199254740992)), (222006709/18014398509481984), by norm_num⟩
  | 1 => ⟨((-542776531/2147483648), (-47270319/2147483648)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((1504896089/4294967296), (131061153/4294967296)), (209/4294967296), by norm_num⟩
  | 3 => ⟨((-347704827/1073741824), (-121126225/4294967296)), (195/4294967296), by norm_num⟩
  | 4 => ⟨((482021241/2147483648), (167916603/8589934592)), (273/8589934592), by norm_num⟩
  | 5 => ⟨((-1069157325/8589934592), (-2909773/268435456)), (153/8589934592), by norm_num⟩
  | 6 => ⟨((988111181/17179869184), (86054441/17179869184)), (143/17179869184), by norm_num⟩
  | 7 => ⟨((-391375131/17179869184), (-8521199/4294967296)), (229/68719476736), by norm_num⟩
  | 8 => ⟨((542561137/68719476736), (94503121/137438953472)), (5/4294967296), by norm_num⟩
  | 9 => ⟨((-1337154569/549755813888), (-29113143/137438953472)), (199/549755813888), by norm_num⟩
  | 10 => ⟨((1482951871/2199023255552), (129150035/2199023255552)), (223/2199023255552), by norm_num⟩
  | 11 => ⟨((-747566479/4398046511104), (-32552721/2199023255552)), (227/8796093022208), by norm_num⟩
  | 12 => ⟨((1381796259/35184372088832), (60170205/17592186044416)), (53/8796093022208), by norm_num⟩
  | 13 => ⟨((-1178816223/140737488355328), (-401027/549755813888)), (91/70368744177664), by norm_num⟩
  | 14 => ⟨((933820733/562949953421312), (81326295/562949953421312)), (291/1125899906842624), by norm_num⟩
  | 15 => ⟨((-690426889/2251799813685248), (-60129165/2251799813685248)), (217/4503599627370496), by norm_num⟩
  | 16 => ⟨((957134903/18014398509481984), (166713445/36028797018963968)), (303/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (56579360651/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222285115992019/79228162514264337593543950336), (33461865021/158456325028528675187087900672)), (184427/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889193184939853/39614081257132168796771975168), (150547210581/39614081257132168796771975168)), (103741/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888934168983461/2475880078570760549798248448), (159917410605/2475880078570760549798248448)), (55113/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885300322969399/77371252455336267181195264), (19984194345/19342813113834066795298816)), (110227/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193625062883529/1208925819614629174706176), (37458719443/2417851639229258349412352)), (103339/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314576279508281/151115727451828646838272), (65529478695/302231454903657293676544)), (90423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58968959478519/2361183241434822606848), (212883545205/75557863725914323419136)), (146939/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648475421150533/2361183241434822606848), (79793173291/2361183241434822606848)), (110207/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810319707891835/295147905179352825856), (219307295221/590295810358705651712)), (303075/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822464705144101/73786976294838206464), (273948355279/73786976294838206464)), (378853/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455380511626593/2305843009213693952), (307936690883/9223372036854775808)), (26639/576460752303423488), by norm_num⟩
  | 6 => ⟨((398193044188359/288230376151711744), (307618004087/1152921504606846976)), (213121/576460752303423488), by norm_num⟩
  | 5 => ⟨((596760306899239/72057594037927936), (33600959527/18014398509481984)), (186491/72057594037927936), by norm_num⟩
  | 4 => ⟨((93128176280757/2251799813685248), (402496471313/36028797018963968)), (559513/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487280814905131/9007199254740992), (250935880535/4503599627370496)), (87433/1125899906842624), by norm_num⟩
  | 2 => ⟨((2224013375052787/4503599627370496), (250001751513/1125899906842624)), (1399149/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210249043705483/2251799813685248), (1490704014457/2251799813685248)), (2099295/2251799813685248), by norm_num⟩
  | 0 => ⟨((271151488929931/281474976710656), (1472195041607/1125899906842624)), (4200977/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((271151488929931/281474976710656), (1472195041607/1125899906842624)), (16025455483443450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044824592910181/1125899906842624), (2836400465803/1125899906842624)), (8104787/2251799813685248), by norm_num⟩
  | 2 => ⟨((1939160627241995/2251799813685248), (10528612513429/2251799813685248)), (7541585/1125899906842624), by norm_num⟩
  | 3 => ⟨((834939470132159/1125899906842624), (18133646447119/2251799813685248)), (26119103/2251799813685248), by norm_num⟩
  | 4 => ⟨((619097405786209/1125899906842624), (6723731418799/562949953421312)), (39159233/2251799813685248), by norm_num⟩
  | 5 => ⟨((1361047323180903/4503599627370496), (59154738758333/4503599627370496)), (22000155/1125899906842624), by norm_num⟩
  | 6 => ⟨((1642197962344069/18014398509481984), (71509375168417/9007199254740992)), (222006709/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1052686123/16777216)), (1/8388608), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1075703853/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((440908474766027/18014398509481984), (-750509362727281/9007199254740992)), (57288865/2251799813685248), by norm_num⟩
  | 1 => ⟨((-148914787/2147483648), (1013924189/4294967296)), (311/4294967296), by norm_num⟩
  | 2 => ⟨((210953681/2147483648), (-1436331771/4294967296)), (443/4294967296), by norm_num⟩
  | 3 => ⟨((-398451189/4294967296), (1356478113/4294967296)), (421/4294967296), by norm_num⟩
  | 4 => ⟨((141112153/2147483648), (-960797973/4294967296)), (75/1073741824), by norm_num⟩
  | 5 => ⟨((-79960167/2147483648), (1088858255/8589934592)), (171/4294967296), by norm_num⟩
  | 6 => ⟨((151029475/8589934592), (-1028322579/17179869184)), (325/17179869184), by norm_num⟩
  | 7 => ⟨((-244513557/34359738368), (416208179/17179869184)), (265/34359738368), by norm_num⟩
  | 8 => ⟨((21648721/8589934592), (-1179206567/137438953472)), (377/137438953472), by norm_num⟩
  | 9 => ⟨((-218081583/274877906944), (1484863903/549755813888)), (477/549755813888), by norm_num⟩
  | 10 => ⟨((61787165/274877906944), (-841387245/1099511627776)), (17/68719476736), by norm_num⟩
  | 11 => ⟨((-127313615/2199023255552), (216711779/1099511627776)), (141/2199023255552), by norm_num⟩
  | 12 => ⟨((480942177/35184372088832), (-12791473/274877906944)), (535/35184372088832), by norm_num⟩
  | 13 => ⟨((-419265167/140737488355328), (1427336743/140737488355328)), (469/140737488355328), by norm_num⟩
  | 14 => ⟨((169695381/281474976710656), (-1155414145/562949953421312)), (191/281474976710656), by norm_num⟩
  | 15 => ⟨((-64104429/562949953421312), (436471303/1125899906842624)), (145/1125899906842624), by norm_num⟩
  | 16 => ⟨((363243047/18014398509481984), (-9661065/140737488355328)), (413/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-1673977074525/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778198275479143/633825300114114700748351602688), (-1979858306851/633825300114114700748351602688)), (92395/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889100104159743/39614081257132168796771975168), (-2226867215727/39614081257132168796771975168)), (103957/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472208785245535/618970019642690137449562112), (-2365456627759/2475880078570760549798248448)), (220937/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885250736112407/77371252455336267181195264), (-2364793379861/154742504910672534362390528)), (110485/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548907373018303/9671406556917033397649408), (-2216289331945/9671406556917033397649408)), (207195/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314555868672241/151115727451828646838272), (-1938548972921/604462909807314587353088)), (90665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943436871699503/37778931862957161709568), (-3148822291701/75557863725914323419136)), (147363/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648425434686993/2361183241434822606848), (-2360462474587/4722366482869645213696)), (110551/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620501542463873/590295810358705651712), (-810940331667/147573952589676412928)), (304107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113893234291719/4611686018427387904), (-2025945833759/36893488147419103232)), (190137/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455331656672813/2305843009213693952), (-4554517430199/9223372036854775808)), (427999/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592575704623117/1152921504606846976), (-1137424029841/288230376151711744)), (428239/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149168440016987/18014398509481984), (-3975566392405/144115188075855872)), (374979/144115188075855872), by norm_num⟩
  | 4 => ⟨((372447206787349/9007199254740992), (-1488132450955/9007199254740992)), (563009/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486949224253591/9007199254740992), (-3710881386081/4503599627370496)), (352355/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223337970648757/4503599627370496), (-7393483710813/2251799813685248)), (1412271/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209205636675767/2251799813685248), (-22039545894513/2251799813685248)), (1062779/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167005431396105/2251799813685248), (-43518402711397/2251799813685248)), (4279857/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167005431396105/2251799813685248), (-43518402711397/2251799813685248)), (16326358803755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084563050319973/2251799813685248), (-83759323957793/2251799813685248)), (8402813/2251799813685248), by norm_num⟩
  | 2 => ⟨((1926631070862969/2251799813685248), (-19384670739941/281474976710656)), (8091309/1125899906842624), by norm_num⟩
  | 3 => ⟨((102358629733125/140737488355328), (-132683584816173/1125899906842624)), (29920505/2251799813685248), by norm_num⟩
  | 4 => ⟨((1159857219147185/2251799813685248), (-48250505563851/281474976710656)), (50574541/2251799813685248), by norm_num⟩
  | 5 => ⟨((265625221025165/1125899906842624), (-397645985158121/2251799813685248)), (138877755/4503599627370496), by norm_num⟩
  | 6 => ⟨((440908474766027/18014398509481984), (-750509362727281/9007199254740992)), (57288865/2251799813685248), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1075703853/16777216)), (1/8388608), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-548702773/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-629677080713727/9007199254740992), (-794785754930479/18014398509481984)), (270810213/9007199254740992), by norm_num⟩
  | 1 => ⟨((433922017/2147483648), (273850715/2147483648)), (375/4294967296), by norm_num⟩
  | 2 => ⟨((-1254195943/4294967296), (-791530373/4294967296)), (17/134217728), by norm_num⟩
  | 3 => ⟨((604182089/2147483648), (762605679/4294967296)), (263/2147483648), by norm_num⟩
  | 4 => ⟨((-27286107/134217728), (-551053479/4294967296)), (191/2147483648), by norm_num⟩
  | 5 => ⟨((1009497511/8589934592), (637099765/8589934592)), (111/2147483648), by norm_num⟩
  | 6 => ⟨((-972607699/17179869184), (-613818389/17179869184)), (215/8589934592), by norm_num⟩
  | 7 => ⟨((803199379/34359738368), (253451905/17179869184)), (357/34359738368), by norm_num⟩
  | 8 => ⟨((-1160772401/137438953472), (-183142557/34359738368)), (259/68719476736), by norm_num⟩
  | 9 => ⟨((372784863/137438953472), (58816675/34359738368)), (335/274877906944), by norm_num⟩
  | 10 => ⟨((-26937171/34359738368), (-136001645/274877906944)), (389/1099511627776), by norm_num⟩
  | 11 => ⟨((226497275/1099511627776), (285887501/2199023255552)), (411/4398046511104), by norm_num⟩
  | 12 => ⟨((-872881769/17592186044416), (-550880773/17592186044416)), (199/8796093022208), by norm_num⟩
  | 13 => ⟨((776293173/70368744177664), (489923147/70368744177664)), (89/17592186044416), by norm_num⟩
  | 14 => ⟨((-320539409/140737488355328), (-809177159/562949953421312)), (295/281474976710656), by norm_num⟩
  | 15 => ⟨((988243259/2251799813685248), (311843041/1125899906842624)), (57/281474976710656), by norm_num⟩
  | 16 => ⟨((-357048801/4503599627370496), (-450671159/9007199254740992)), (83/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-3358933514205/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889057984482831/316912650057057350374175801344), (-993094696227/158456325028528675187087900672)), (92591/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472251794237123/9903520314283042199192993792), (-4467942384507/39614081257132168796771975168)), (52095/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944367981235735/1237940039285380274899124224), (-4745979770033/2475880078570760549798248448)), (221463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885200897733837/77371252455336267181195264), (-296538744799/9671406556917033397649408)), (27691/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548813397090459/9671406556917033397649408), (-1111659171285/2417851639229258349412352)), (207753/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258140717255323/604462909807314587353088), (-972340753509/151115727451828646838272)), (181853/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886738272638677/75557863725914323419136), (-3158754045277/37778931862957161709568)), (147821/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324187100278631/1180591620717411303424), (-591970433075/590295810358705651712)), (110923/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620359244548407/590295810358705651712), (-6507829007967/590295810358705651712)), (38153/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911055886730657/36893488147419103232), (-8129020425539/73786976294838206464)), (381809/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821121268536395/9223372036854775808), (-71384566451/72057594037927936)), (429919/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592366746876531/1152921504606846976), (-9127326989069/1152921504606846976)), (6725/18014398509481984), by norm_num⟩
  | 5 => ⟨((149145080438467/18014398509481984), (-3987642896991/72057594037927936)), (377141/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489500462313213/36028797018963968), (-11940701512887/36028797018963968)), (566795/36028797018963968), by norm_num⟩
  | 3 => ⟨((743287371102673/4503599627370496), (-14887032132973/9007199254740992)), (710393/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111273586577773/2251799813685248), (-14828870621405/2251799813685248)), (713247/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103957855120741/1125899906842624), (-5524567980897/281474976710656)), (1077025/1125899906842624), by norm_num⟩
  | 0 => ⟨((270501969350541/281474976710656), (-87237254101235/2251799813685248)), (1091395/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((270501969350541/281474976710656), (-87237254101235/2251799813685248)), (4163341524364280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((519068549091697/562949953421312), (-167672802114663/2251799813685248)), (8729041/2251799813685248), by norm_num⟩
  | 2 => ⟨((950972716113789/1125899906842624), (-309205738758313/2251799813685248)), (1087325/140737488355328), by norm_num⟩
  | 3 => ⟨((390997039000393/562949953421312), (-522331016172763/2251799813685248)), (34166305/2251799813685248), by norm_num⟩
  | 4 => ⟨((241276916408087/562949953421312), (-181392572697107/562949953421312)), (63310973/2251799813685248), by norm_num⟩
  | 5 => ⟨((359694993246077/4503599627370496), (-1243900004501703/4503599627370496)), (190138517/4503599627370496), by norm_num⟩
  | 6 => ⟨((-629677080713727/9007199254740992), (-794785754930479/18014398509481984)), (270810213/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-548702773/8388608)), (1/8388608), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-558966793/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1122326223875125/18014398509481984), (436050899076211/9007199254740992)), (520186315/18014398509481984), by norm_num⟩
  | 1 => ⟨((787883063/4294967296), (-306111637/2147483648)), (367/4294967296), by norm_num⟩
  | 2 => ⟨((-1159936801/4294967296), (225331759/1073741824)), (271/2147483648), by norm_num⟩
  | 3 => ⟨((1138454377/4294967296), (-884634153/4294967296)), (267/2147483648), by norm_num⟩
  | 4 => ⟨((-838027361/4294967296), (651187821/4294967296)), (395/4294967296), by norm_num⟩
  | 5 => ⟨((987008171/8589934592), (-766953121/8589934592)), (467/8589934592), by norm_num⟩
  | 6 => ⟨((-242182111/4294967296), (94093611/2147483648)), (115/4294967296), by norm_num⟩
  | 7 => ⟨((6366879/268435456), (-316631881/17179869184)), (389/34359738368), by norm_num⟩
  | 8 => ⟨((-1199800749/137438953472), (233075813/34359738368)), (575/137438953472), by norm_num⟩
  | 9 => ⟨((392526677/137438953472), (-152506113/68719476736)), (189/137438953472), by norm_num⟩
  | 10 => ⟨((-462308339/549755813888), (359235955/549755813888)), (447/1099511627776), by norm_num⟩
  | 11 => ⟨((989991777/4398046511104), (-384635763/2199023255552)), (481/4398046511104), by norm_num⟩
  | 12 => ⟨((-121457099/2199023255552), (188756089/4398046511104)), (475/17592186044416), by norm_num⟩
  | 13 => ⟨((440151405/35184372088832), (-342018945/35184372088832)), (27/4398046511104), by norm_num⟩
  | 14 => ⟨((-740570831/281474976710656), (575459379/281474976710656)), (365/281474976710656), by norm_num⟩
  | 15 => ⟨((1162968331/2251799813685248), (-903682681/2251799813685248)), (9/35184372088832), by norm_num⟩
  | 16 => ⟨((-856072321/9007199254740992), (166302407/2251799813685248)), (213/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1615892424831/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444511190377855/158456325028528675187087900672), (1910857243063/316912650057057350374175801344)), (2893/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((944463560933565/19807040628566084398385987584), (16790888993/154742504910672534362390528)), (208345/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944325486081169/1237940039285380274899124224), (1141484287891/618970019642690137449562112)), (221423/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770316881856893/154742504910672534362390528), (4564604740871/154742504910672534362390528)), (110743/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774366936014821/4835703278458516698824704), (4277901635591/9671406556917033397649408)), (103855/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258071214228407/604462909807314587353088), (3741749046281/604462909807314587353088)), (90907/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886625482745419/75557863725914323419136), (3038845096151/37778931862957161709568)), (295573/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296663942052453/4722366482869645213696), (4555948038479/4722366482869645213696)), (110895/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620243329853563/590295810358705651712), (6260660883173/590295810358705651712)), (76285/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455491801132957/18446744073709551616), (7820177555989/73786976294838206464)), (381693/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455239768512909/2305843009213693952), (8789937801201/9223372036854775808)), (214887/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592205108529139/1152921504606846976), (8780242570265/1152921504606846976)), (430237/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193019834490073/144115188075855872), (7671815020987/144115188075855872)), (188489/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489290495065877/36028797018963968), (11485952839503/36028797018963968)), (283255/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486314457855303/9007199254740992), (14319399799005/9007199254740992)), (709965/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111016551747333/2251799813685248), (28524898646137/4503599627370496)), (712711/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207160765672493/2251799813685248), (42503375187933/2251799813685248)), (1075953/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081284990185017/1125899906842624), (83875535199679/2251799813685248)), (4359137/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081284990185017/1125899906842624), (83875535199679/2251799813685248)), (16628788002974700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2073751754579963/2251799813685248), (5034492670261/70368744177664)), (8697545/2251799813685248), by norm_num⟩
  | 2 => ⟨((949127868828245/1125899906842624), (296730832143729/2251799813685248)), (4316049/562949953421312), by norm_num⟩
  | 3 => ⟨((390279548545655/562949953421312), (31267821923665/140737488355328)), (33657237/2251799813685248), by norm_num⟩
  | 4 => ⟨((242784102168869/562949953421312), (693671121574307/2251799813685248)), (30811417/1125899906842624), by norm_num⟩
  | 5 => ⟨((51284121321709/562949953421312), (1196641509095929/4503599627370496)), (182236733/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1122326223875125/18014398509481984), (436050899076211/9007199254740992)), (520186315/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-558966793/8388608)), (1/8388608), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1137408433/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((168596819372989/9007199254740992), (1317349842892619/18014398509481984)), (101201255/9007199254740992), by norm_num⟩
  | 1 => ⟨((-60209147/1073741824), (-940901623/4294967296)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((180370485/2147483648), (1409344679/4294967296)), (221/4294967296), by norm_num⟩
  | 3 => ⟨((-360227789/4294967296), (-351834945/1073741824)), (223/4294967296), by norm_num⟩
  | 4 => ⟨((269786503/4294967296), (263500825/1073741824)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((-161641627/4294967296), (-1263004681/8589934592)), (51/2147483648), by norm_num⟩
  | 6 => ⟨((322823359/17179869184), (630603981/8589934592)), (103/8589934592), by norm_num⟩
  | 7 => ⟨((-138156051/17179869184), (-539748771/17179869184)), (89/17179869184), by norm_num⟩
  | 8 => ⟨((413878541/137438953472), (1616942813/137438953472)), (269/137438953472), by norm_num⟩
  | 9 => ⟨((-17220407/17179869184), (-1076428393/274877906944)), (181/274877906944), by norm_num⟩
  | 10 => ⟨((165080733/549755813888), (1289876511/1099511627776)), (219/1099511627776), by norm_num⟩
  | 11 => ⟨((-359663767/4398046511104), (-351284063/1099511627776)), (15/274877906944), by norm_num⟩
  | 12 => ⟨((179576059/8796093022208), (350784335/4398046511104)), (121/8796093022208), by norm_num⟩
  | 13 => ⟨((-331053413/70368744177664), (-646680587/35184372088832)), (225/70368744177664), by norm_num⟩
  | 14 => ⟨((141678199/140737488355328), (138377279/35184372088832)), (195/281474976710656), by norm_num⟩
  | 15 => ⟨((-113181321/562949953421312), (-221088683/281474976710656)), (157/1125899906842624), by norm_num⟩
  | 16 => ⟨((42382617/1125899906842624), (662322503/4503599627370496)), (237/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1719724529555/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777982229364267/633825300114114700748351602688), (1016747125877/316912650057057350374175801344)), (92401/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888857099476229/39614081257132168796771975168), (2287168608133/39614081257132168796771975168)), (25991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472144251551121/618970019642690137449562112), (2429476196265/2475880078570760549798248448)), (110477/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885121701173769/77371252455336267181195264), (2428756001171/154742504910672534362390528)), (110493/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774332750725245/4835703278458516698824704), (2276193819977/9671406556917033397649408)), (103605/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258011905992953/604462909807314587353088), (1990904972091/604462909807314587353088)), (90673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886530073469253/75557863725914323419136), (3233787576441/75557863725914323419136)), (9211/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((162074153742889/590295810358705651712), (2424087464231/4722366482869645213696)), (55281/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620147471833125/590295810358705651712), (3331085020181/590295810358705651712)), (76035/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821849435645327/73786976294838206464), (2080402786327/36893488147419103232)), (95079/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820829402847437/9223372036854775808), (292294691509/576460752303423488)), (214027/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592078953384427/1152921504606846976), (1167870329945/288230376151711744)), (107075/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192913394101047/144115188075855872), (4081665420481/144115188075855872)), (1465/1125899906842624), by norm_num⟩
  | 4 => ⟨((1489138699740313/36028797018963968), (6110754710791/36028797018963968)), (140779/18014398509481984), by norm_num⟩
  | 3 => ⟨((5805228205931/35184372088832), (7617932954213/9007199254740992)), (352435/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221721922152991/4503599627370496), (15174496513237/4503599627370496)), (706335/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206795430231579/2251799813685248), (22608886634171/2251799813685248)), (265795/562949953421312), by norm_num⟩
  | 0 => ⟨((1081120151342485/1125899906842624), (44609722263573/2251799813685248)), (1070575/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081120151342485/1125899906842624), (44609722263573/2251799813685248)), (4083919529441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037679519918457/1125899906842624), (85670971978651/2251799813685248)), (4196819/2251799813685248), by norm_num⟩
  | 2 => ⟨((1909483961523253/2251799813685248), (157916369889495/2251799813685248)), (8055293/2251799813685248), by norm_num⟩
  | 3 => ⟨((201016504521615/281474976710656), (267820233160489/2251799813685248)), (7395647/1125899906842624), by norm_num⟩
  | 4 => ⟨((1116600575768133/2251799813685248), (382529827263663/2251799813685248)), (6161241/562949953421312), by norm_num⟩
  | 5 => ⟨((977411731159491/4503599627370496), (758740670951657/4503599627370496)), (16407327/1125899906842624), by norm_num⟩
  | 6 => ⟨((168596819372989/9007199254740992), (1317349842892619/18014398509481984)), (101201255/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1137408433/16777216)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-288983225/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((636734078279419/9007199254740992), (279519789848057/18014398509481984)), (24764233/2251799813685248), by norm_num⟩
  | 1 => ⟨((-115546655/536870912), (-202895229/4294967296)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((1407137535/4294967296), (308859539/4294967296)), (7/134217728), by norm_num⟩
  | 3 => ⟨((-178502575/536870912), (-156721633/2147483648)), (115/2147483648), by norm_num⟩
  | 4 => ⟨((543455095/2147483648), (931919/16777216)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((-1323648985/8589934592), (-290534227/8589934592)), (109/4294967296), by norm_num⟩
  | 6 => ⟨((335823253/4294967296), (294845991/17179869184)), (223/17179869184), by norm_num⟩
  | 7 => ⟨((-1168481633/34359738368), (-128237891/17179869184)), (49/8589934592), by norm_num⟩
  | 8 => ⟨((444683569/34359738368), (12200723/4294967296)), (151/68719476736), by norm_num⟩
  | 9 => ⟨((-601710713/137438953472), (-33018111/34359738368)), (207/274877906944), by norm_num⟩
  | 10 => ⟨((732768707/549755813888), (321678015/1099511627776)), (127/549755813888), by norm_num⟩
  | 11 => ⟨((-811247553/2199023255552), (-356129431/4398046511104)), (283/4398046511104), by norm_num⟩
  | 12 => ⟨((411643563/4398046511104), (361414681/17592186044416)), (289/17592186044416), by norm_num⟩
  | 13 => ⟨((-1542471463/70368744177664), (-42320581/8796093022208)), (273/70368744177664), by norm_num⟩
  | 14 => ⟨((335434927/70368744177664), (36813131/35184372088832)), (239/281474976710656), by norm_num⟩
  | 15 => ⟨((-1089321773/1125899906842624), (-119550297/562949953421312)), (49/281474976710656), by norm_num⟩
  | 16 => ⟨((829116145/4503599627370496), (181986781/4503599627370496)), (301/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (281453332773/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777919572170007/633825300114114700748351602688), (332782339537/633825300114114700748351602688)), (92233/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944393372517259/19807040628566084398385987584), (374295453573/39614081257132168796771975168)), (207529/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888502433366233/2475880078570760549798248448), (397582458799/2475880078570760549798248448)), (27563/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770169030396543/154742504910672534362390528), (397462751617/154742504910672534362390528)), (110255/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48393624719687/302231454903657293676544), (372494191665/9671406556917033397649408)), (103367/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39310978046229/18889465931478580854784), (325805337029/604462909807314587353088)), (180899/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235803997978077/9444732965739290427392), (264597759047/37778931862957161709568)), (146985/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296520011620617/4722366482869645213696), (49586046867/590295810358705651712)), (27561/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620047362907709/590295810358705651712), (272554157507/295147905179352825856)), (303187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821725147645341/73786976294838206464), (680878491471/73786976294838206464)), (2961/576460752303423488), by norm_num⟩
  | 7 => ⟨((1820690743042047/9223372036854775808), (765291959209/9223372036854775808)), (426417/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795970872897609/576460752303423488), (95552812377/144115188075855872)), (426459/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596397483524323/72057594037927936), (333946437619/72057594037927936)), (373199/144115188075855872), by norm_num⟩
  | 4 => ⟨((744482153985931/18014398509481984), (124986126677/4503599627370496)), (559893/36028797018963968), by norm_num⟩
  | 3 => ⟨((742963046580285/4503599627370496), (1246455706759/9007199254740992)), (700035/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221314160729825/4503599627370496), (620681130485/1125899906842624)), (1400581/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206225698965343/2251799813685248), (231170219379/140737488355328)), (1051085/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161266553966217/2251799813685248), (1824153811053/562949953421312)), (4209655/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161266553966217/2251799813685248), (1824153811053/562949953421312)), (16058559426314543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074349526237189/2251799813685248), (7003255968241/1125899906842624)), (8108095/2251799813685248), by norm_num⟩
  | 2 => ⟨((238849483226379/281474976710656), (12902746160249/1125899906842624)), (15039161/2251799813685248), by norm_num⟩
  | 3 => ⟨((1621136521630819/2251799813685248), (43795214602605/2251799813685248)), (25868073/2251799813685248), by norm_num⟩
  | 4 => ⟨((1166251806658273/2251799813685248), (63058910861839/2251799813685248)), (38252581/2251799813685248), by norm_num⟩
  | 5 => ⟨((602259064972179/2251799813685248), (130637844930211/4503599627370496)), (83531953/4503599627370496), by norm_num⟩
  | 6 => ⟨((636734078279419/9007199254740992), (279519789848057/18014398509481984)), (24764233/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-288983225/4194304)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile023Terms2

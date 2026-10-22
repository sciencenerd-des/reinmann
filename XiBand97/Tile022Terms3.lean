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
namespace Reinmann.XiBand97.Tile022Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28609/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28609/1280))
  have he : value ((69/80), (28609/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1159091107/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((156502791563961/2251799813685248), (17423059454005/9007199254740992)), (5001847/562949953421312), by norm_num⟩
  | 1 => ⟨((-922692819/4294967296), (-51360527/8589934592)), (119/4294967296), by norm_num⟩
  | 2 => ⟨((1426041337/4294967296), (2480587/268435456)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-183664763/536870912), (-40893865/4294967296)), (97/2147483648), by norm_num⟩
  | 4 => ⟨((1135431159/4294967296), (1975073/268435456)), (19/536870912), by norm_num⟩
  | 5 => ⟨((-701933183/4294967296), (-39072221/8589934592)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((1446470179/17179869184), (40257965/17179869184)), (99/8589934592), by norm_num⟩
  | 7 => ⟨((-159682169/4294967296), (-35554023/34359738368)), (177/34359738368), by norm_num⟩
  | 8 => ⟨((987168727/68719476736), (54949497/137438953472)), (69/34359738368), by norm_num⟩
  | 9 => ⟨((-678084543/137438953472), (-37744717/274877906944)), (191/274877906944), by norm_num⟩
  | 10 => ⟨((209598811/137438953472), (46668209/1099511627776)), (119/549755813888), by norm_num⟩
  | 11 => ⟨((-942369197/2199023255552), (-52455787/4398046511104)), (135/2199023255552), by norm_num⟩
  | 12 => ⟨((1941935463/17592186044416), (6755961/2199023255552)), (35/2199023255552), by norm_num⟩
  | 13 => ⟨((-461738843/17592186044416), (-51404215/70368744177664)), (67/17592186044416), by norm_num⟩
  | 14 => ⟨((1631147847/281474976710656), (45397889/281474976710656)), (119/140737488355328), by norm_num⟩
  | 15 => ⟨((-1344519265/1125899906842624), (-37420481/1125899906842624)), (99/562949953421312), by norm_num⟩
  | 16 => ⟨((259747883/1125899906842624), (14458537/2251799813685248)), (77/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (2265297341/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777857835642765/633825300114114700748351602688), (42851920189/633825300114114700748351602688)), (23051/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888717310476811/39614081257132168796771975168), (48197351651/39614081257132168796771975168)), (207461/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472107170837191/618970019642690137449562112), (51195768447/2475880078570760549798248448)), (55107/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442523826896733/38685626227668133590597632), (25590059609/77371252455336267181195264)), (220429/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774263452395299/4835703278458516698824704), (47964741233/9671406556917033397649408)), (103327/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257890875899039/604462909807314587353088), (41952535665/604462909807314587353088)), (90411/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471583463218071/18889465931478580854784), (68141737431/75557863725914323419136)), (146919/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296446460724759/4722366482869645213696), (51079077853/4722366482869645213696)), (220381/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619946307256855/590295810358705651712), (70189521377/590295810358705651712)), (303025/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821598943220787/73786976294838206464), (87670638715/73786976294838206464)), (378785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820548921206201/9223372036854775808), (49269221485/4611686018427387904)), (213069/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591800121375361/1152921504606846976), (49212394963/576460752303423488)), (426145/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298167816853895/36028797018963968), (42997004287/72057594037927936)), (186443/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488779201095725/36028797018963968), (64368044815/18014398509481984)), (559345/36028797018963968), by norm_num⟩
  | 3 => ⟨((742847741029545/4503599627370496), (160474989025/9007199254740992)), (349607/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110427623994791/2251799813685248), (159809285205/2251799813685248)), (5463/17592186044416), by norm_num⟩
  | 1 => ⟨((1102771537771155/1125899906842624), (476113160259/2251799813685248)), (131129/140737488355328), by norm_num⟩
  | 0 => ⟨((539981030702127/562949953421312), (469525076627/1125899906842624)), (4197343/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539981030702127/562949953421312), (469525076627/1125899906842624)), (16011592873580168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2071796660663111/2251799813685248), (450367982583/562949953421312)), (2013919/562949953421312), by norm_num⟩
  | 2 => ⟨((953090530460821/1125899906842624), (828733421785/562949953421312)), (7418171/1125899906842624), by norm_num⟩
  | 3 => ⟨((806802457782531/1125899906842624), (5612278475409/2251799813685248)), (25162039/2251799813685248), by norm_num⟩
  | 4 => ⟨((578135167709447/1125899906842624), (8043343889099/2251799813685248)), (18093441/1125899906842624), by norm_num⟩
  | 5 => ⟨((1187402525805229/4503599627370496), (8260307936803/2251799813685248)), (74843035/4503599627370496), by norm_num⟩
  | 6 => ⟨((156502791563961/2251799813685248), (17423059454005/9007199254740992)), (5001847/562949953421312), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1159091107/16777216)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-587879901/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((342835876070259/9007199254740992), (-991378919491625/18014398509481984)), (153098623/9007199254740992), by norm_num⟩
  | 1 => ⟨((-512580827/4294967296), (185278825/1073741824)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((803597109/4294967296), (-145235171/536870912)), (181/2147483648), by norm_num⟩
  | 3 => ⟨((-419945681/2147483648), (303589359/1073741824)), (95/1073741824), by norm_num⟩
  | 4 => ⟨((658368627/4294967296), (-951902679/4294967296)), (75/1073741824), by norm_num⟩
  | 5 => ⟨((-825724409/8589934592), (1193874137/8589934592)), (379/8589934592), by norm_num⟩
  | 6 => ⟨((215754509/4294967296), (-623897575/8589934592)), (199/8589934592), by norm_num⟩
  | 7 => ⟨((-386569723/17179869184), (139730517/4294967296)), (359/34359738368), by norm_num⟩
  | 8 => ⟨((606043565/68719476736), (-109531057/8589934592)), (283/68719476736), by norm_num⟩
  | 9 => ⟨((-844553819/274877906944), (1221098651/274877906944)), (99/68719476736), by norm_num⟩
  | 10 => ⟨((529618723/549755813888), (-765749551/549755813888)), (125/274877906944), by norm_num⟩
  | 11 => ⟨((-150965131/549755813888), (873092105/2199023255552)), (287/2199023255552), by norm_num⟩
  | 12 => ⟨((631133727/8796093022208), (-456262541/4398046511104)), (151/4398046511104), by norm_num⟩
  | 13 => ⟨((-608897277/35184372088832), (880374497/35184372088832)), (293/35184372088832), by norm_num⟩
  | 14 => ⟨((545483969/140737488355328), (-394344163/70368744177664)), (265/140737488355328), by norm_num⟩
  | 15 => ⟨((-57012061/70368744177664), (329723691/281474976710656)), (223/562949953421312), by norm_num⟩
  | 16 => ⟨((357521975/2251799813685248), (-516923363/2251799813685248)), (351/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-1257941137687/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777797606440653/633825300114114700748351602688), (-743580352817/316912650057057350374175801344)), (184693/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888649503271627/39614081257132168796771975168), (-836332860953/19807040628566084398385987584)), (207799/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944178285328991/1237940039285380274899124224), (-888358630143/1237940039285380274899124224)), (27601/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((27656611234791/2417851639229258349412352), (-1776166205331/154742504910672534362390528)), (220833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548459147480297/9671406556917033397649408), (-832285276671/4835703278458516698824704)), (207057/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628915753901769/302231454903657293676544), (-1455914230819/604462909807314587353088)), (181201/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471559307264473/18889465931478580854784), (-591191074429/18889465931478580854784)), (294501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296373861219639/4722366482869645213696), (-1772614490455/4722366482869645213696)), (220919/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1581881122419/576460752303423488), (-1217894010439/295147905179352825856)), (303833/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455368394018255/18446744073709551616), (-95075046403/2305843009213693952)), (47487/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820407444446407/9223372036854775808), (-854873999171/2305843009213693952)), (427527/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591658097668989/1152921504606846976), (-426936664755/144115188075855872)), (106927/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192546383349669/144115188075855872), (-186503731343/9007199254740992)), (374449/144115188075855872), by norm_num⟩
  | 4 => ⟨((744295326659833/18014398509481984), (-4467110781633/36028797018963968)), (281041/18014398509481984), by norm_num⟩
  | 3 => ⟨((371364417637729/2251799813685248), (-2784104809765/4503599627370496)), (703319/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220373289036899/4503599627370496), (-2772379585031/1125899906842624)), (1408793/4503599627370496), by norm_num⟩
  | 1 => ⟨((275600556506563/281474976710656), (-16517498815607/2251799813685248)), (1059303/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158385058545567/2251799813685248), (-32570713757035/2251799813685248)), (4259027/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158385058545567/2251799813685248), (-32570713757035/2251799813685248)), (16246898659712981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2068374453737801/2251799813685248), (-31219534477311/1125899906842624)), (1035987/281474976710656), by norm_num⟩
  | 2 => ⟨((949079535748793/1125899906842624), (-114705911561075/2251799813685248)), (7842599/1125899906842624), by norm_num⟩
  | 3 => ⟨((1594213834082545/2251799813685248), (-48345786614957/562949953421312)), (3505217/281474976710656), by norm_num⟩
  | 4 => ⟨((278013246584659/562949953421312), (-68455038829611/562949953421312)), (5565251/281474976710656), by norm_num⟩
  | 5 => ⟨((1031782985242257/4503599627370496), (-540905136577381/4503599627370496)), (109604515/4503599627370496), by norm_num⟩
  | 6 => ⟨((342835876070259/9007199254740992), (-991378919491625/18014398509481984)), (153098623/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-587879901/8388608)), (1/8388608), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1191718971/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-394226349231637/18014398509481984), (-546514927313311/9007199254740992)), (409875759/18014398509481984), by norm_num⟩
  | 1 => ⟨((298708095/4294967296), (414098229/2147483648)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-474655203/4294967296), (-1316026463/4294967296)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((502826595/4294967296), (697067157/2147483648)), (265/2147483648), by norm_num⟩
  | 4 => ⟨((-12484453/134217728), (-553829237/2147483648)), (423/4294967296), by norm_num⟩
  | 5 => ⟨((507856175/8589934592), (704039651/4294967296)), (135/2147483648), by norm_num⟩
  | 6 => ⟨((-537998087/17179869184), (-745825303/8589934592)), (287/8589934592), by norm_num⟩
  | 7 => ⟨((488510537/34359738368), (338610423/8589934592)), (523/34359738368), by norm_num⟩
  | 8 => ⟨((-97032049/17179869184), (-134515269/8589934592)), (209/34359738368), by norm_num⟩
  | 9 => ⟨((34263675/17179869184), (1519988501/274877906944)), (593/274877906944), by norm_num⟩
  | 10 => ⟨((-348453771/549755813888), (-966121055/549755813888)), (379/549755813888), by norm_num⟩
  | 11 => ⟨((201346335/1099511627776), (558251767/1099511627776)), (55/274877906944), by norm_num⟩
  | 12 => ⟨((-213296497/4398046511104), (-295692361/2199023255552)), (117/2199023255552), by norm_num⟩
  | 13 => ⟨((52143673/4398046511104), (578293071/17592186044416)), (459/35184372088832), by norm_num⟩
  | 14 => ⟨((-47347257/17592186044416), (-1050198005/140737488355328)), (419/140737488355328), by norm_num⟩
  | 15 => ⟨((160503607/281474976710656), (445011439/281474976710656)), (357/562949953421312), by norm_num⟩
  | 16 => ⟨((-510089103/4503599627370496), (-353567577/1125899906842624)), (569/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-624259556163/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444434397820435/158456325028528675187087900672), (-2951864610387/633825300114114700748351602688)), (92491/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888581811224393/39614081257132168796771975168), (-3320057095215/39614081257132168796771975168)), (104071/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888284411100213/2475880078570760549798248448), (-55102718819/38685626227668133590597632)), (110597/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769950693453073/154742504910672534362390528), (-27542691059/1208925819614629174706176)), (221243/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193548870763937/1208925819614629174706176), (-1651972222939/4835703278458516698824704)), (207467/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257771566991683/604462909807314587353088), (-2889773375113/604462909807314587353088)), (90793/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886139296867947/75557863725914323419136), (-1173418486663/18889465931478580854784)), (147587/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648149975172841/2361183241434822606848), (-3518324635465/4722366482869645213696)), (110733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619743892702181/590295810358705651712), (-302160039947/36893488147419103232)), (152327/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227668060423857/9223372036854775808), (-3019250221031/36893488147419103232)), (381025/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455065168941739/2305843009213693952), (-3393427638379/4611686018427387904)), (214469/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591509409442989/1152921504606846976), (-6778791025945/1152921504606846976)), (26831/72057594037927936), by norm_num⟩
  | 5 => ⟨((596207064069205/72057594037927936), (-2961190359611/72057594037927936)), (376037/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488387980632073/36028797018963968), (-138523052033/562949953421312)), (282431/18014398509481984), by norm_num⟩
  | 3 => ⟨((185649607334309/1125899906842624), (-11050237524491/9007199254740992)), (176873/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109914698393277/2251799813685248), (-22005898465995/4503599627370496)), (354809/1125899906842624), by norm_num⟩
  | 1 => ⟨((137745840390245/140737488355328), (-32773256295755/2251799813685248)), (16715/17592186044416), by norm_num⟩
  | 0 => ⟨((1078212691550839/1125899906842624), (-16152308615717/562949953421312)), (2160955/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078212691550839/1125899906842624), (-16152308615717/562949953421312)), (8243389133933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1031618364001861/1125899906842624), (-15468181533251/281474976710656)), (8525725/2251799813685248), by norm_num⟩
  | 2 => ⟨((941831692375269/1125899906842624), (-226766305323397/2251799813685248)), (4140157/562949953421312), by norm_num⟩
  | 3 => ⟨((97054719533913/140737488355328), (-379386643197005/2251799813685248)), (31041873/2251799813685248), by norm_num⟩
  | 4 => ⟨((503483506534991/1125899906842624), (-130815409173117/562949953421312)), (53273863/2251799813685248), by norm_num⟩
  | 5 => ⟨((164352936810497/1125899906842624), (-233993805378285/1125899906842624)), (144810729/4503599627370496), by norm_num⟩
  | 6 => ⟨((-394226349231637/18014398509481984), (-546514927313311/9007199254740992)), (409875759/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1191718971/16777216)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-603513281/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-266877871870707/4503599627370496), (-344593628497363/18014398509481984)), (24786145/1125899906842624), by norm_num⟩
  | 1 => ⟨((819250803/4294967296), (132227433/2147483648)), (153/2147483648), by norm_num⟩
  | 2 => ⟨((-659266651/2147483648), (-53202961/536870912)), (495/4294967296), by norm_num⟩
  | 3 => ⟨((1414731657/4294967296), (57084575/536870912)), (533/4294967296), by norm_num⟩
  | 4 => ⟨((-1138461383/4294967296), (-367496317/4294967296)), (431/4294967296), by norm_num⟩
  | 5 => ⟨((732913165/4294967296), (118292501/2147483648)), (557/8589934592), by norm_num⟩
  | 6 => ⟨((-1572770979/17179869184), (-507691829/17179869184)), (75/2147483648), by norm_num⟩
  | 7 => ⟨((723222069/17179869184), (58364177/4294967296)), (277/17179869184), by norm_num⟩
  | 8 => ⟨((-1163981017/68719476736), (-375734077/68719476736)), (7/1073741824), by norm_num⟩
  | 9 => ⟨((416301151/68719476736), (134382371/68719476736)), (161/68719476736), by norm_num⟩
  | 10 => ⟨((-1072017369/549755813888), (-86512033/137438953472)), (13/17179869184), by norm_num⟩
  | 11 => ⟨((313699163/549755813888), (202524721/1099511627776)), (489/2199023255552), by norm_num⟩
  | 12 => ⟨((-673172435/4398046511104), (-217300643/4398046511104)), (527/8796093022208), by norm_num⟩
  | 13 => ⟨((1333451371/35184372088832), (430439253/35184372088832)), (131/8796093022208), by norm_num⟩
  | 14 => ⟨((-613173483/70368744177664), (-395865859/140737488355328)), (121/35184372088832), by norm_num⟩
  | 15 => ⟨((1052655627/562949953421312), (339798145/562949953421312)), (417/562949953421312), by norm_num⟩
  | 16 => ⟨((-423545969/1125899906842624), (-273442009/2251799813685248)), (169/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-3685545684943/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777677866507919/633825300114114700748351602688), (-544575114303/79228162514264337593543950336)), (92629/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888514336288665/39614081257132168796771975168), (-2449990064437/19807040628566084398385987584)), (208471/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944106166909189/1237940039285380274899124224), (-5204752309343/2475880078570760549798248448)), (221565/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884939091690673/77371252455336267181195264), (-2601545781601/77371252455336267181195264)), (221637/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548322528486361/9671406556917033397649408), (-4876134291663/9671406556917033397649408)), (207861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257711225093969/604462909807314587353088), (-4264854011227/604462909807314587353088)), (181955/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886040381675541/75557863725914323419136), (-6927082396153/75557863725914323419136)), (73955/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296225012763975/4722366482869645213696), (-2596210387843/2361183241434822606848)), (221991/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619639634665307/590295810358705651712), (-3567441433861/295147905179352825856)), (152721/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821212335729321/73786976294838206464), (-8911563905719/73786976294838206464)), (95527/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455027376317979/2305843009213693952), (-10015836123317/9223372036854775808)), (430293/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591355116205139/1152921504606846976), (-10003753967327/1152921504606846976)), (430821/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149034452384759/18014398509481984), (-8739705265945/144115188075855872)), (377563/144115188075855872), by norm_num⟩
  | 4 => ⟨((744086619279949/18014398509481984), (-13082431414863/36028797018963968)), (567535/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484916278172253/9007199254740992), (-2038205110833/1125899906842624)), (711505/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219232014106351/4503599627370496), (-32469378510099/4503599627370496)), (1429283/4503599627370496), by norm_num⟩
  | 1 => ⟨((550736911190753/562949953421312), (-12087582821055/562949953421312)), (269957/281474976710656), by norm_num⟩
  | 0 => ⟨((2154099806849323/2251799813685248), (-47645923659099/1125899906842624)), (2191265/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154099806849323/2251799813685248), (-47645923659099/1125899906842624)), (8359012608054732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1028303096384903/1125899906842624), (-91157370497561/1125899906842624)), (8755687/2251799813685248), by norm_num⟩
  | 2 => ⟨((1863571682461095/2251799813685248), (-166511082861383/1125899906842624)), (17411221/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493025992974937/2251799813685248), (-551213010944463/2251799813685248)), (33968723/2251799813685248), by norm_num⟩
  | 4 => ⟨((427500442215919/1125899906842624), (-730948948485077/2251799813685248)), (61675279/2251799813685248), by norm_num⟩
  | 5 => ⟨((174740352931999/4503599627370496), (-1110155518498713/4503599627370496)), (21719049/562949953421312), by norm_num⟩
  | 6 => ⟨((-266877871870707/4503599627370496), (-344593628497363/18014398509481984)), (24786145/1125899906842624), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-603513281/8388608)), (1/8388608), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1221733697/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-916269559524545/18014398509481984), (145012664143137/4503599627370496)), (396443991/18014398509481984), by norm_num⟩
  | 1 => ⟨((177937429/1073741824), (-450577983/4294967296)), (309/4294967296), by norm_num⟩
  | 2 => ⟨((-1159474643/4294967296), (734013283/4294967296)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((629613387/2147483648), (-398581023/2147483648)), (551/4294967296), by norm_num⟩
  | 4 => ⟨((-512835299/2147483648), (324653863/2147483648)), (451/4294967296), by norm_num⟩
  | 5 => ⟨((668346765/4294967296), (-423101451/4294967296)), (295/4294967296), by norm_num⟩
  | 6 => ⟨((-362923047/4294967296), (459501791/8589934592)), (161/4294967296), by norm_num⟩
  | 7 => ⟨((337839521/8589934592), (-213871599/8589934592)), (151/8589934592), by norm_num⟩
  | 8 => ⟨((-550356887/34359738368), (174203579/17179869184)), (247/34359738368), by norm_num⟩
  | 9 => ⟨((398470193/68719476736), (-252254257/68719476736)), (359/137438953472), by norm_num⟩
  | 10 => ⟨((-1038603485/549755813888), (657494977/549755813888)), (235/274877906944), by norm_num⟩
  | 11 => ⟨((615249167/1099511627776), (-48685957/137438953472)), (559/2199023255552), by norm_num⟩
  | 12 => ⟨((-334090197/2199023255552), (13218629/137438953472)), (305/4398046511104), by norm_num⟩
  | 13 => ⟨((669844993/17592186044416), (-212024957/8796093022208)), (307/17592186044416), by norm_num⟩
  | 14 => ⟨((-1247096945/140737488355328), (789483175/140737488355328)), (287/70368744177664), by norm_num⟩
  | 15 => ⟨((1083509931/562949953421312), (-685923307/562949953421312)), (501/562949953421312), by norm_num⟩
  | 16 => ⟨((-882544989/2251799813685248), (17459409/70368744177664)), (205/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (3357117666097/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888813757155547/316912650057057350374175801344), (3968151712805/633825300114114700748351602688)), (92591/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888457799219643/39614081257132168796771975168), (4463073663187/39614081257132168796771975168)), (52095/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118009525499297/154742504910672534362390528), (4740655026927/2475880078570760549798248448)), (221463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884909210151811/77371252455336267181195264), (4739124661429/154742504910672534362390528)), (27691/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548266673393759/9671406556917033397649408), (4441303862503/9671406556917033397649408)), (25969/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257662524533277/604462909807314587353088), (121391123141/18889465931478580854784)), (181853/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942980783330645/37778931862957161709568), (788661606261/9444732965739290427392)), (295641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296166184162607/4722366482869645213696), (2364652993007/2361183241434822606848)), (110923/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619559204073439/590295810358705651712), (3249234780371/295147905179352825856)), (38153/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821112484566615/73786976294838206464), (4058300828339/36893488147419103232)), (381809/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819998115780127/9223372036854775808), (9122266019009/9223372036854775808)), (429919/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591244903051523/1152921504606846976), (4555568556397/576460752303423488)), (6725/18014398509481984), by norm_num⟩
  | 5 => ⟨((1192180502523117/144115188075855872), (3979869109223/72057594037927936)), (377141/144115188075855872), by norm_num⟩
  | 4 => ⟨((46501037346371/1125899906842624), (5957313482667/18014398509481984)), (566797/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484745809492035/9007199254740992), (14849642621537/9007199254740992)), (177599/2251799813685248), by norm_num⟩
  | 2 => ⟨((2218904757076089/4503599627370496), (14784330005215/2251799813685248)), (1426507/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202490692489191/2251799813685248), (44027469229037/2251799813685248)), (1077047/1125899906842624), by norm_num⟩
  | 0 => ⟨((2153320036235183/2251799813685248), (86759102747733/2251799813685248)), (136431/70368744177664), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153320036235183/2251799813685248), (86759102747733/2251799813685248)), (520442962914919831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2055804431818541/2251799813685248), (20741199232841/281474976710656)), (8686137/2251799813685248), by norm_num⟩
  | 2 => ⟨((233080179144213/281474976710656), (151487175884689/1125899906842624)), (8570161/1125899906842624), by norm_num⟩
  | 3 => ⟨((751641907915307/1125899906842624), (501766210351977/2251799813685248)), (2062441/140737488355328), by norm_num⟩
  | 4 => ⟨((222943097437341/562949953421312), (334975169092993/1125899906842624)), (1836441/70368744177664), by norm_num⟩
  | 5 => ⟨((307686800024043/4503599627370496), (530636169757691/2251799813685248)), (20378449/562949953421312), by norm_num⟩
  | 6 => ⟨((-916269559524545/18014398509481984), (145012664143137/4503599627370496)), (396443991/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1221733697/16777216)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-77242857/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-170240624217517/18014398509481984), (258952828989775/4503599627370496)), (44635235/2251799813685248), by norm_num⟩
  | 1 => ⟨((66886583/2147483648), (-1627857743/8589934592)), (563/8589934592), by norm_num⟩
  | 2 => ⟨((-110223633/2147483648), (670644195/2147483648)), (233/2147483648), by norm_num⟩
  | 3 => ⟨((242186075/4294967296), (-368388977/1073741824)), (257/2147483648), by norm_num⟩
  | 4 => ⟨((-199551449/4294967296), (1214149971/4294967296)), (213/2147483648), by norm_num⟩
  | 5 => ⟨((263075609/8589934592), (-800328047/4294967296)), (563/8589934592), by norm_num⟩
  | 6 => ⟨((-289018097/17179869184), (1758500455/17179869184)), (621/17179869184), by norm_num⟩
  | 7 => ⟨((34019875/4294967296), (-1655923037/34359738368)), (587/34359738368), by norm_num⟩
  | 8 => ⟨((-56061979/17179869184), (170551631/8589934592)), (243/34359738368), by norm_num⟩
  | 9 => ⟨((164241011/137438953472), (-499653647/68719476736)), (357/137438953472), by norm_num⟩
  | 10 => ⟨((-27065579/68719476736), (164677691/68719476736)), (59/68719476736), by norm_num⟩
  | 11 => ⟨((259501769/2199023255552), (-1578911433/2199023255552)), (71/274877906944), by norm_num⟩
  | 12 => ⟨((-35636479/1099511627776), (1734611503/8796093022208)), (313/4398046511104), by norm_num⟩
  | 13 => ⟨((72278167/8796093022208), (-879537929/17592186044416)), (637/35184372088832), by norm_num⟩
  | 14 => ⟨((-136124027/70368744177664), (1656464875/140737488355328)), (301/70368744177664), by norm_num⟩
  | 15 => ⟨((119638023/281474976710656), (-727925067/281474976710656)), (531/562949953421312), by norm_num⟩
  | 16 => ⟨((-197153703/2251799813685248), (74972571/140737488355328)), (439/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (564582774093/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777582022501037/633825300114114700748351602688), (2669229767017/633825300114114700748351602688)), (92463/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888406885985283/39614081257132168796771975168), (750536393613/9903520314283042199192993792)), (52019/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888098668697515/2475880078570760549798248448), (1594427341761/1237940039285380274899124224)), (3455/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1769765081076965/154742504910672534362390528), (3187814541817/154742504910672534362390528)), (55291/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387054273145663/2417851639229258349412352), (2987471403713/9671406556917033397649408)), (51847/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314404891409567/151115727451828646838272), (1306466611499/302231454903657293676544)), (22689/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471473138299827/18889465931478580854784), (1060986753897/18889465931478580854784)), (73761/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648057559309349/2361183241434822606848), (3181150480217/4722366482869645213696)), (221361/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809745058005847/295147905179352825856), (4371142901281/590295810358705651712)), (19031/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821027812306949/73786976294838206464), (5459523411359/73786976294838206464)), (380807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909952587867087/4611686018427387904), (383494501423/576460752303423488)), (428667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591154851567889/1152921504606846976), (3064177640675/576460752303423488)), (428991/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192104947847189/144115188075855872), (2676910282003/72057594037927936)), (93933/36028797018963968), by norm_num⟩
  | 4 => ⟨((371981580176813/9007199254740992), (4006888883467/18014398509481984)), (70541/4503599627370496), by norm_num⟩
  | 3 => ⟨((742311732757573/4503599627370496), (9987616186659/9007199254740992)), (706691/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109346804608731/2251799813685248), (19886661333227/4503599627370496)), (88577/281474976710656), by norm_num⟩
  | 1 => ⟨((1101128549763523/1125899906842624), (29609427014565/2251799813685248)), (2135511/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076590529312201/1125899906842624), (911589906153/35184372088832)), (4309877/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076590529312201/1125899906842624), (911589906153/35184372088832)), (16440876015670012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2057369790513443/2251799813685248), (27893323123775/562949953421312)), (8465577/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874199398041623/2251799813685248), (203879154809829/2251799813685248)), (254815/35184372088832), by norm_num⟩
  | 3 => ⟨((1541458815636437/2251799813685248), (84845506002699/562949953421312)), (30100045/2251799813685248), by norm_num⟩
  | 4 => ⟨((502024005051643/1125899906842624), (116161172409863/562949953421312)), (12570699/562949953421312), by norm_num⟩
  | 5 => ⟨((703630681704071/4503599627370496), (828715897749445/4503599627370496)), (16397989/562949953421312), by norm_num⟩
  | 6 => ⟨((-170240624217517/18014398509481984), (258952828989775/4503599627370496)), (44635235/2251799813685248), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-77242857/1048576)), (1/8388608), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile022Terms3

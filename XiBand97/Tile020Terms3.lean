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
namespace Reinmann.XiBand97.Tile020Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27893/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27893/1280))
  have he : value ((69/80), (27893/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1130082431/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-231724068551237/18014398509481984), (1230885099903705/18014398509481984)), (213600255/9007199254740992), by norm_num⟩
  | 1 => ⟨((170771821/4294967296), (-907115483/4294967296)), (79/1073741824), by norm_num⟩
  | 2 => ⟨((-131965737/2147483648), (700983117/2147483648)), (245/2147483648), by norm_num⟩
  | 3 => ⟨((135970565/2147483648), (-1444512383/4294967296)), (507/4294967296), by norm_num⟩
  | 4 => ⟨((-105072697/2147483648), (1116262275/4294967296)), (197/2147483648), by norm_num⟩
  | 5 => ⟨((129913667/4294967296), (-673909/4194304)), (489/8589934592), by norm_num⟩
  | 6 => ⟨((-33464055/2147483648), (1422050187/17179869184)), (505/17179869184), by norm_num⟩
  | 7 => ⟨((29553947/4294967296), (-627945357/17179869184)), (7/536870912), by norm_num⟩
  | 8 => ⟨((-91352505/34359738368), (485251439/34359738368)), (87/17179869184), by norm_num⟩
  | 9 => ⟨((125499765/137438953472), (-1333273599/274877906944)), (15/8589934592), by norm_num⟩
  | 10 => ⟨((-310340081/1099511627776), (1648482119/1099511627776)), (149/274877906944), by norm_num⟩
  | 11 => ⟨((174413521/2199023255552), (-926459675/2199023255552)), (21/137438953472), by norm_num⟩
  | 12 => ⟨((-179706533/8796093022208), (238643849/2199023255552)), (87/2199023255552), by norm_num⟩
  | 13 => ⟨((42729271/8796093022208), (-226971775/8796093022208)), (333/35184372088832), by norm_num⟩
  | 14 => ⟨((-150946275/140737488355328), (1603610039/281474976710656)), (295/140737488355328), by norm_num⟩
  | 15 => ⟨((31105423/140737488355328), (-165227557/140737488355328)), (61/140737488355328), by norm_num⟩
  | 16 => ⟨((-96148183/2251799813685248), (510725393/2251799813685248)), (379/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (1144263906783/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777853910201101/633825300114114700748351602688), (338213779387/79228162514264337593543950336)), (184933/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944356339837479/19807040628566084398385987584), (1521609515863/19807040628566084398385987584)), (52021/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888423475464845/2475880078570760549798248448), (1616270337001/1237940039285380274899124224)), (221129/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770089776467855/154742504910672534362390528), (201971973757/9671406556917033397649408)), (110587/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548521376209639/9671406556917033397649408), (3028529061133/9671406556917033397649408)), (103699/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257885695549781/604462909807314587353088), (331114099517/75557863725914323419136)), (181521/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943162396324401/37778931862957161709568), (134453599143/2361183241434822606848)), (73765/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296439104340917/4722366482869645213696), (3225165150099/4722366482869645213696)), (110687/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619935281508135/590295810358705651712), (553975840839/73786976294838206464)), (304515/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455395949287017/18446744073709551616), (2767784125053/36893488147419103232)), (190417/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820530010091673/9223372036854775808), (6221757480693/9223372036854775808)), (428701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397944718966743/288230376151711744), (97102632427/18014398509481984)), (107257/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192650058724735/144115188075855872), (5429669395597/144115188075855872)), (375769/144115188075855872), by norm_num⟩
  | 4 => ⟨((744371084292015/18014398509481984), (8128372055375/36028797018963968)), (70549/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485640098331207/9007199254740992), (10132287942065/9007199254740992)), (706787/9007199254740992), by norm_num⟩
  | 2 => ⟨((555179341178679/1125899906842624), (10090129963969/2251799813685248)), (708735/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205269030766827/2251799813685248), (30060352495783/2251799813685248)), (2135979/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159110552971311/2251799813685248), (14821264607839/562949953421312)), (538905/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159110552971311/2251799813685248), (14821264607839/562949953421312)), (2055759431005382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2068675747057323/2251799813685248), (113689498075919/2251799813685248)), (8494571/2251799813685248), by norm_num⟩
  | 2 => ⟨((473675992261937/562949953421312), (208887758081721/2251799813685248)), (128635/17592186044416), by norm_num⟩
  | 3 => ⟨((196857476700223/281474976710656), (351523667350515/2251799813685248)), (15381575/1125899906842624), by norm_num⟩
  | 4 => ⟨((261636772668249/562949953421312), (491696014784047/2251799813685248)), (52634897/2251799813685248), by norm_num⟩
  | 5 => ⟨((758056588205135/4503599627370496), (457041545736337/2251799813685248)), (71911605/2251799813685248), by norm_num⟩
  | 6 => ⟨((-231724068551237/18014398509481984), (1230885099903705/18014398509481984)), (213600255/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1130082431/16777216)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-286583489/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((849943081586047/18014398509481984), (427368304791025/9007199254740992)), (69351639/9007199254740992), by norm_num⟩
  | 1 => ⟨((-317691757/2147483648), (-159741741/1073741824)), (53/2147483648), by norm_num⟩
  | 2 => ⟨((498060333/2147483648), (500869305/2147483648)), (21/536870912), by norm_num⟩
  | 3 => ⟨((-1041110195/4294967296), (-65436367/268435456)), (89/2147483648), by norm_num⟩
  | 4 => ⟨((816098749/4294967296), (820701401/4294967296)), (71/2147483648), by norm_num⟩
  | 5 => ⟨((-1023549163/8589934592), (-514660899/4294967296)), (45/2147483648), by norm_num⟩
  | 6 => ⟨((1069777493/17179869184), (33619089/536870912)), (95/8589934592), by norm_num⟩
  | 7 => ⟨((-119795755/4294967296), (-963771055/34359738368)), (173/34359738368), by norm_num⟩
  | 8 => ⟨((375618897/34359738368), (377737321/34359738368)), (137/68719476736), by norm_num⟩
  | 9 => ⟨((-523444835/137438953472), (-526396971/137438953472)), (193/274877906944), by norm_num⟩
  | 10 => ⟨((656503301/549755813888), (660205863/549755813888)), (61/274877906944), by norm_num⟩
  | 11 => ⟨((-374265873/1099511627776), (-752753333/2199023255552)), (141/2199023255552), by norm_num⟩
  | 12 => ⟨((782338987/8796093022208), (98343905/1099511627776)), (75/4398046511104), by norm_num⟩
  | 13 => ⟨((-377387595/17592186044416), (-189757997/8796093022208)), (147/35184372088832), by norm_num⟩
  | 14 => ⟨((338084749/70368744177664), (339991487/70368744177664)), (67/70368744177664), by norm_num⟩
  | 15 => ⟨((-565366813/562949953421312), (-284277691/281474976710656)), (57/281474976710656), by norm_num⟩
  | 16 => ⟨((443176093/2251799813685248), (55709441/281474976710656)), (181/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1026731708379/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777798002458399/633825300114114700748351602688), (1213820747397/633825300114114700748351602688)), (2885/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944324985202537/19807040628566084398385987584), (1365230268893/39614081257132168796771975168)), (25967/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888357096002995/2475880078570760549798248448), (1450157201011/2475880078570760549798248448)), (110369/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885011838487381/77371252455336267181195264), (1449707474555/154742504910672534362390528)), (110379/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548459705168817/9671406556917033397649408), (42456972341/302231454903657293676544)), (51745/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257832030360827/604462909807314587353088), (1188317799025/604462909807314587353088)), (45283/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886238142982083/75557863725914323419136), (1930121707359/75557863725914323419136)), (36797/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648187301633385/2361183241434822606848), (180851107797/590295810358705651712)), (110409/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619847381524973/590295810358705651712), (1988091615229/590295810358705651712)), (151841/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910737551919101/36893488147419103232), (2483210165243/73786976294838206464)), (189843/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820409351956625/9223372036854775808), (2790995388073/9223372036854775808)), (213633/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795830120300925/576460752303423488), (696932245631/288230376151711744)), (213707/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596274261258971/72057594037927936), (2435593171989/144115188075855872)), (187077/144115188075855872), by norm_num⟩
  | 4 => ⟨((372148597102285/9007199254740992), (14242433245/140737488355328)), (280783/36028797018963968), by norm_num⟩
  | 3 => ⟨((92841453519585/562949953421312), (2272392397157/4503599627370496)), (351271/9007199254740992), by norm_num⟩
  | 2 => ⟨((555096798640875/1125899906842624), (4525650181207/2251799813685248)), (10991/70368744177664), by norm_num⟩
  | 1 => ⟨((551208021788013/562949953421312), (13481669433605/2251799813685248)), (528679/1125899906842624), by norm_num⟩
  | 0 => ⟨((539616772213319/562949953421312), (26584557258961/2251799813685248)), (530917/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539616772213319/562949953421312), (26584557258961/2251799813685248)), (2025287630321311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2068688969004953/2251799813685248), (6370669760081/281474976710656)), (4121437/2251799813685248), by norm_num⟩
  | 2 => ⟨((474828685565863/562949953421312), (46820980009887/1125899906842624)), (7759147/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598111720070489/2251799813685248), (157967465916899/2251799813685248)), (3433619/562949953421312), by norm_num⟩
  | 4 => ⟨((280776218890383/562949953421312), (112110169446403/1125899906842624)), (21421823/2251799813685248), by norm_num⟩
  | 5 => ⟨((1075663825688693/4503599627370496), (111831857468023/1125899906842624)), (51269501/4503599627370496), by norm_num⟩
  | 6 => ⟨((849943081586047/18014398509481984), (427368304791025/9007199254740992)), (69351639/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-286583489/4194304)), (1/16777216), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-580946857/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1150707372181039/18014398509481984), (-20156117690191/2251799813685248)), (82596979/9007199254740992), by norm_num⟩
  | 1 => ⟨((-871899121/4294967296), (244358929/8589934592)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((692735585/2147483648), (-97073229/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-1467700653/4294967296), (102834649/2147483648)), (27/536870912), by norm_num⟩
  | 4 => ⟨((72881745/268435456), (-163407025/4294967296)), (173/4294967296), by norm_num⟩
  | 5 => ⟨((-185297687/1073741824), (207726529/8589934592)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((785181365/8589934592), (-55013841/4294967296)), (237/17179869184), by norm_num⟩
  | 7 => ⟨((-1425913511/34359738368), (199813655/34359738368)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((566453737/34359738368), (-79377319/34359738368)), (87/34359738368), by norm_num⟩
  | 9 => ⟨((-400048993/68719476736), (224235905/274877906944)), (31/34359738368), by norm_num⟩
  | 10 => ⟨((1017101787/549755813888), (-142526755/549755813888)), (5/17179869184), by norm_num⟩
  | 11 => ⟨((-146927465/274877906944), (164711891/2199023255552)), (187/2199023255552), by norm_num⟩
  | 12 => ⟨((1245182381/8796093022208), (-21810969/1099511627776)), (25/1099511627776), by norm_num⟩
  | 13 => ⟨((-608808713/17592186044416), (170625067/35184372088832)), (197/35184372088832), by norm_num⟩
  | 14 => ⟨((552807675/70368744177664), (-154930185/140737488355328)), (45/35184372088832), by norm_num⟩
  | 15 => ⟨((-468494013/281474976710656), (262600783/1125899906842624)), (307/1125899906842624), by norm_num⟩
  | 16 => ⟨((186112399/562949953421312), (-13039991/281474976710656)), (123/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-181354427665/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888871120563963/316912650057057350374175801344), (-107193736899/316912650057057350374175801344)), (92221/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944293647788115/19807040628566084398385987584), (-241129121289/39614081257132168796771975168)), (207501/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944145289422887/1237940039285380274899124224), (-256128104721/2475880078570760549798248448)), (110237/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769957243933635/154742504910672534362390528), (-64011903307/38685626227668133590597632)), (220477/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548397513501389/9671406556917033397649408), (-239959150963/9671406556917033397649408)), (206701/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628888850943779/302231454903657293676544), (-209878810923/604462909807314587353088)), (180867/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943075013187611/37778931862957161709568), (-170446470853/37778931862957161709568)), (73479/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162038582740487/590295810358705651712), (-255529681461/4722366482869645213696)), (55111/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809878474660637/295147905179352825856), (-175562965911/295147905179352825856)), (303121/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910681209395661/36893488147419103232), (-219283312259/36893488147419103232)), (378917/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820283068867737/9223372036854775808), (-61614915073/1152921504606846976)), (6661/144115188075855872), by norm_num⟩
  | 6 => ⟨((1591534565768213/1152921504606846976), (-492334836751/1152921504606846976)), (106583/288230376151711744), by norm_num⟩
  | 5 => ⟨((596219619818177/72057594037927936), (-430136373237/144115188075855872)), (23317/9007199254740992), by norm_num⟩
  | 4 => ⟨((744215912534153/18014398509481984), (-321946838435/18014398509481984)), (69959/4503599627370496), by norm_num⟩
  | 3 => ⟨((46414450762447/281474976710656), (-50161143395/562949953421312)), (699703/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219992609814651/4503599627370496), (-1598311107475/4503599627370496)), (174969/562949953421312), by norm_num⟩
  | 1 => ⟨((1102128888168809/1125899906842624), (-1190212984823/1125899906842624)), (525129/562949953421312), by norm_num⟩
  | 0 => ⟨((2157387948570331/2251799813685248), (-4693125461365/2251799813685248)), (2102359/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157387948570331/2251799813685248), (-4693125461365/2251799813685248)), (8019863132957076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516731183975983/562949953421312), (-4496355426421/1125899906842624)), (8074379/2251799813685248), by norm_num⟩
  | 2 => ⟨((948596089465749/1125899906842624), (-16508800108791/2251799813685248)), (14887421/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598306208857731/2251799813685248), (-13909036788969/1125899906842624)), (6326067/562949953421312), by norm_num⟩
  | 4 => ⟨((1134118972981029/2251799813685248), (-39490011010627/2251799813685248)), (36546665/2251799813685248), by norm_num⟩
  | 5 => ⟨((570506479349719/2251799813685248), (-79556575958829/4503599627370496)), (38095301/2251799813685248), by norm_num⟩
  | 6 => ⟨((1150707372181039/18014398509481984), (-20156117690191/2251799813685248)), (82596979/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-580946857/8388608)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-147102275/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((578659510274719/18014398509481984), (-480488999842203/9007199254740992)), (147285287/18014398509481984), by norm_num⟩
  | 1 => ⟨((-444086339/4294967296), (184373191/1073741824)), (115/4294967296), by norm_num⟩
  | 2 => ⟨((357364695/2147483648), (-1186948815/4294967296)), (187/4294967296), by norm_num⟩
  | 3 => ⟨((-191718763/1073741824), (1273546949/4294967296)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((617118891/4294967296), (-256211843/1073741824)), (83/2147483648), by norm_num⟩
  | 5 => ⟨((-49660727/536870912), (329885643/2147483648)), (27/1073741824), by norm_num⟩
  | 6 => ⟨((106567809/2147483648), (-707907281/8589934592)), (117/8589934592), by norm_num⟩
  | 7 => ⟨((-196016311/8589934592), (162761831/4294967296)), (217/34359738368), by norm_num⟩
  | 8 => ⟨((630952165/68719476736), (-523910123/34359738368)), (11/4294967296), by norm_num⟩
  | 9 => ⟨((-451323705/137438953472), (749511835/137438953472)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((581101985/549755813888), (-965034211/549755813888)), (167/549755813888), by norm_num⟩
  | 11 => ⟨((-42511253/137438953472), (564786417/1099511627776)), (99/1099511627776), by norm_num⟩
  | 12 => ⟨((364902519/4398046511104), (-1183579/8589934592)), (107/4398046511104), by norm_num⟩
  | 13 => ⟨((-722815937/35184372088832), (600189059/17592186044416)), (107/17592186044416), by norm_num⟩
  | 14 => ⟨((664758499/140737488355328), (-275990579/35184372088832)), (199/140737488355328), by norm_num⟩
  | 15 => ⟨((-570606683/562949953421312), (118450587/70368744177664)), (173/562949953421312), by norm_num⟩
  | 16 => ⟨((229589007/1125899906842624), (-381277731/1125899906842624)), (141/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-83757310167/633825300114114700748351602688)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777686703422503/633825300114114700748351602688), (-198015276573/79228162514264337593543950336)), (92357/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888524758248505/39614081257132168796771975168), (-1781711521191/39614081257132168796771975168)), (103911/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888224054344293/2475880078570760549798248448), (-1892532600101/2475880078570760549798248448)), (55209/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769890631144011/154742504910672534362390528), (-1891930029515/154742504910672534362390528)), (110431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548334970294019/9671406556917033397649408), (-1773044430665/9671406556917033397649408)), (103543/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257722882964345/604462909807314587353088), (-1550774196593/604462909807314587353088)), (45307/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886060770306591/75557863725914323419136), (-2518809288703/75557863725914323419136)), (147273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296241566681631/4722366482869645213696), (-944029326345/2361183241434822606848)), (55239/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50614513900835/18446744073709551616), (-2594378297949/590295810358705651712)), (18993/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821246416065139/73786976294838206464), (-1620210688759/36893488147419103232)), (94993/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820152055282749/9223372036854775808), (-3641969039021/9223372036854775808)), (213811/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795701457864257/576460752303423488), (-1818796356467/576460752303423488)), (213907/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596161666081535/72057594037927936), (-3177977037661/144115188075855872)), (93639/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488256542274921/36028797018963968), (-2378574655877/18014398509481984)), (140567/18014398509481984), by norm_num⟩
  | 3 => ⟨((742520423066561/4503599627370496), (-92645253627/140737488355328)), (351799/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219542080764449/4503599627370496), (-11807322993419/4503599627370496)), (352373/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203563731912653/2251799813685248), (-17583340457833/2251799813685248)), (1060005/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155927932232841/2251799813685248), (-17329635396007/1125899906842624)), (2131627/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155927932232841/2251799813685248), (-17329635396007/1125899906842624)), (8131511696822356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2063604391335767/2251799813685248), (-66367258365685/2251799813685248)), (4147363/2251799813685248), by norm_num⟩
  | 2 => ⟨((944590732511693/1125899906842624), (-60820577820461/1125899906842624)), (7845961/2251799813685248), by norm_num⟩
  | 3 => ⟨((789193163495627/1125899906842624), (-204105369601897/2251799813685248)), (7006323/1125899906842624), by norm_num⟩
  | 4 => ⟨((1087860643936895/2251799813685248), (-17883312866403/140737488355328)), (22184411/2251799813685248), by norm_num⟩
  | 5 => ⟨((489194766287911/2251799813685248), (-138232907791079/1125899906842624)), (54145561/4503599627370496), by norm_num⟩
  | 6 => ⟨((578659510274719/18014398509481984), (-480488999842203/9007199254740992)), (147285287/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-147102275/2097152)), (1/16777216), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1191157259/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-83393611651107/4503599627370496), (-1031860823209245/18014398509481984)), (380647861/18014398509481984), by norm_num⟩
  | 1 => ⟨((518235087/8589934592), (200384985/1073741824)), (593/8589934592), by norm_num⟩
  | 2 => ⟨((-211057493/2147483648), (-326436813/1073741824)), (485/4294967296), by norm_num⟩
  | 3 => ⟨((229215229/2147483648), (709041767/2147483648)), (529/4294967296), by norm_num⟩
  | 4 => ⟨((-23337667/268435456), (-1155063263/4294967296)), (433/4294967296), by norm_num⟩
  | 5 => ⟨((486632781/8589934592), (188165381/1073741824)), (567/8589934592), by norm_num⟩
  | 6 => ⟨((-132124715/4294967296), (-817414635/8589934592)), (309/8589934592), by norm_num⟩
  | 7 => ⟨((122992879/8589934592), (380459399/8589934592)), (577/34359738368), by norm_num⟩
  | 8 => ⟨((-400722673/68719476736), (-1239573451/68719476736)), (59/8589934592), by norm_num⟩
  | 9 => ⟨((72532953/34359738368), (897477771/137438953472)), (343/137438953472), by norm_num⟩
  | 10 => ⟨((-378110981/549755813888), (-146203461/68719476736)), (449/549755813888), by norm_num⟩
  | 11 => ⟨((447971665/2199023255552), (1385730881/2199023255552)), (267/1099511627776), by norm_num⟩
  | 12 => ⟨((-121627911/2199023255552), (-1504948329/8796093022208)), (291/4398046511104), by norm_num⟩
  | 13 => ⟨((487723663/35184372088832), (94293595/2199023255552)), (293/17592186044416), by norm_num⟩
  | 14 => ⟨((-113503627/35184372088832), (-351105869/35184372088832)), (137/35184372088832), by norm_num⟩
  | 15 => ⟨((394459493/562949953421312), (1220199271/562949953421312)), (239/281474976710656), by norm_num⟩
  | 16 => ⟨((-321296777/2251799813685248), (-993881755/2251799813685248)), (391/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-1226712973707/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777631450918933/633825300114114700748351602688), (-1449988851119/316912650057057350374175801344)), (184971/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888462441532387/39614081257132168796771975168), (-3261680443591/39614081257132168796771975168)), (104065/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944078814352323/1237940039285380274899124224), (-1732270924999/1237940039285380274899124224)), (221181/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769823964926063/154742504910672534362390528), (-1731712249517/77371252455336267181195264)), (221229/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193534026916355/1208925819614629174706176), (-3245773716981/9671406556917033397649408)), (207453/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257667717247385/604462909807314587353088), (-2838865740279/604462909807314587353088)), (45393/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885970648210065/75557863725914323419136), (-4610933624833/75557863725914323419136)), (147575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296173557579459/4722366482869645213696), (-3456255953737/4722366482869645213696)), (110723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619570254857199/590295810358705651712), (-2374597225487/295147905179352825856)), (304625/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910563832112927/36893488147419103232), (-2965880118773/36893488147419103232)), (380985/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227502133452713/1152921504606846976), (-6666728155949/9223372036854775808)), (428889/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591266192648919/1152921504606846976), (-3329304398905/576460752303423488)), (429241/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192201753139161/144115188075855872), (-5817159796653/144115188075855872)), (187991/72057594037927936), by norm_num⟩
  | 4 => ⟨((744035148044447/18014398509481984), (-2176880575931/9007199254740992)), (282383/18014398509481984), by norm_num⟩
  | 3 => ⟨((742400643095301/4503599627370496), (-1356573286221/1125899906842624)), (707347/9007199254740992), by norm_num⟩
  | 2 => ⟨((277380354813321/562949953421312), (-21609977782807/4503599627370496)), (709437/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202765030455547/2251799813685248), (-8044467565111/562949953421312)), (133675/140737488355328), by norm_num⟩
  | 0 => ⟨((2154133967956449/2251799813685248), (-31706341864381/1125899906842624)), (269985/140737488355328), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154133967956449/2251799813685248), (-31706341864381/1125899906842624)), (1029911041796636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1029459180889283/1125899906842624), (-121324653452075/2251799813685248)), (4254051/1125899906842624), by norm_num⟩
  | 2 => ⟨((938010813230343/1125899906842624), (-221864799180425/2251799813685248)), (16475471/2251799813685248), by norm_num⟩
  | 3 => ⟨((1541093099281111/2251799813685248), (-369680429746241/2251799813685248)), (1918669/140737488355328), by norm_num⟩
  | 4 => ⟨((994006797101263/2251799813685248), (-253002933812677/1125899906842624)), (13024753/562949953421312), by norm_num⟩
  | 5 => ⟨((650153330827607/4503599627370496), (-446730005692263/2251799813685248)), (69410415/2251799813685248), by norm_num⟩
  | 6 => ⟨((-83393611651107/4503599627370496), (-1031860823209245/18014398509481984)), (380647861/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1191157259/16777216)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1204955089/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-237908504527037/4503599627370496), (-221517295025825/9007199254740992)), (94717975/4503599627370496), by norm_num⟩
  | 1 => ⟨((373891649/2147483648), (348131593/4294967296)), (75/1073741824), by norm_num⟩
  | 2 => ⟨((-1232285881/4294967296), (-573692469/4294967296)), (31/268435456), by norm_num⟩
  | 3 => ⟨((338451103/1073741824), (157566399/1073741824)), (547/4294967296), by norm_num⟩
  | 4 => ⟨((-1115479623/4294967296), (-519313147/4294967296)), (453/4294967296), by norm_num⟩
  | 5 => ⟨((735287773/4294967296), (342314283/4294967296)), (75/1073741824), by norm_num⟩
  | 6 => ⟨((-807796183/8589934592), (-188035339/4294967296)), (331/8589934592), by norm_num⟩
  | 7 => ⟨((380337777/8589934592), (354133601/17179869184)), (313/17179869184), by norm_num⟩
  | 8 => ⟨((-1253531267/68719476736), (-583583289/68719476736)), (259/34359738368), by norm_num⟩
  | 9 => ⟨((918096569/137438953472), (213710591/68719476736)), (381/137438953472), by norm_num⟩
  | 10 => ⟨((-1210358607/549755813888), (-140871049/137438953472)), (505/549755813888), by norm_num⟩
  | 11 => ⟨((1450598007/2199023255552), (675327995/2199023255552)), (19/68719476736), by norm_num⟩
  | 12 => ⟨((-398411199/2199023255552), (-370961817/4398046511104)), (335/4398046511104), by norm_num⟩
  | 13 => ⟨((808060503/17592186044416), (376193733/17592186044416)), (341/17592186044416), by norm_num⟩
  | 14 => ⟨((-95115557/8796093022208), (-177124739/35184372088832)), (323/70368744177664), by norm_num⟩
  | 15 => ⟨((1337537533/562949953421312), (38918283/35184372088832)), (285/281474976710656), by norm_num⟩
  | 16 => ⟨((-551038189/1125899906842624), (-513073247/2251799813685248)), (59/281474976710656), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-881178247489/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777576532072025/633825300114114700748351602688), (-4166027226077/633825300114114700748351602688)), (185221/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888400411825691/39614081257132168796771975168), (-1171403603813/9903520314283042199192993792)), (208427/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888091387925987/2475880078570760549798248448), (-2488509988681/1237940039285380274899124224)), (221515/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769757348626309/154742504910672534362390528), (-4975394441389/154742504910672534362390528)), (221583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548209363920267/9671406556917033397649408), (-2331352842193/4835703278458516698824704)), (3247/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1257612324040475/604462909807314587353088), (-4078141462219/604462909807314587353088)), (181905/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942939944222705/37778931862957161709568), (-1655936215979/18889465931478580854784)), (295733/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162013104505169/590295810358705651712), (-2482489635873/2361183241434822606848)), (6935/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1619474705323463/590295810358705651712), (-426390695225/36893488147419103232)), (305335/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821006644008033/73786976294838206464), (-2130231243403/18446744073709551616)), (190981/36893488147419103232), by norm_num⟩
  | 7 => ⟨((454969686856941/2305843009213693952), (-9576575028365/9223372036854775808)), (215055/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198890645471093/144115188075855872), (-9564753137499/1152921504606846976)), (430615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192075315034727/144115188075855872), (-1044484151067/18014398509481984)), (377357/144115188075855872), by norm_num⟩
  | 4 => ⟨((743937293406187/18014398509481984), (-3126818207973/9007199254740992)), (283587/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484546111244379/9007199254740992), (-15587729133155/9007199254740992)), (710963/9007199254740992), by norm_num⟩
  | 2 => ⟨((277312635546637/562949953421312), (-15518341833277/2251799813685248)), (178491/562949953421312), by norm_num⟩
  | 1 => ⟨((550468655919257/562949953421312), (-46209177377927/2251799813685248)), (134809/140737488355328), by norm_num⟩
  | 0 => ⟨((1076023219884361/1125899906842624), (-22760372026757/562949953421312)), (2187191/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076023219884361/1125899906842624), (-22760372026757/562949953421312)), (8343471531394576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2053031223409935/2251799813685248), (-174016810163359/2251799813685248)), (4357459/1125899906842624), by norm_num⟩
  | 2 => ⟨((464590072421685/562949953421312), (-19832021839393/140737488355328)), (2154781/281474976710656), by norm_num⟩
  | 3 => ⟨((744474668397913/1125899906842624), (-523741645260545/2251799813685248)), (33310941/2251799813685248), by norm_num⟩
  | 4 => ⟨((862716483391649/2251799813685248), (-692623536624953/2251799813685248)), (59547595/2251799813685248), by norm_num⟩
  | 5 => ⟨((234969703453199/4503599627370496), (-1061440254501929/4503599627370496)), (164520415/4503599627370496), by norm_num⟩
  | 6 => ⟨((-237908504527037/4503599627370496), (-221517295025825/9007199254740992)), (94717975/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1204955089/16777216)), (1/8388608), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile020Terms3

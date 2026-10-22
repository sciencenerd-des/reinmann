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
namespace Reinmann.XiBand97.Tile006Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10993/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10993/640))
  have he : value ((69/80), (10993/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-1781521695/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1191424724923661/18014398509481984), (-386369259187747/18014398509481984)), (221071949/18014398509481984), by norm_num⟩
  | 1 => ⟨((3429823/16777216), (284739443/4294967296)), (165/4294967296), by norm_num⟩
  | 2 => ⟨((-21203457/67108864), (-440070853/4294967296)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((1398203429/4294967296), (56678237/536870912)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-1080476539/4294967296), (-175194837/2147483648)), (209/4294967296), by norm_num⟩
  | 5 => ⟨((1335919541/8589934592), (433227743/8589934592)), (65/2147483648), by norm_num⟩
  | 6 => ⟨((-1376461339/17179869184), (-446375115/17179869184)), (135/8589934592), by norm_num⟩
  | 7 => ⟨((151953587/4294967296), (394218409/34359738368)), (241/34359738368), by norm_num⟩
  | 8 => ⟨((-939389977/68719476736), (-76159115/17179869184)), (47/17179869184), by norm_num⟩
  | 9 => ⟨((80658175/17179869184), (418508547/274877906944)), (65/68719476736), by norm_num⟩
  | 10 => ⟨((-398908549/274877906944), (-258725537/549755813888)), (81/274877906944), by norm_num⟩
  | 11 => ⟨((896758735/2199023255552), (145405749/1099511627776)), (23/274877906944), by norm_num⟩
  | 12 => ⟨((-923973107/8796093022208), (-299636895/8796093022208)), (191/8796093022208), by norm_num⟩
  | 13 => ⟨((878781569/35184372088832), (142490825/17592186044416)), (183/35184372088832), by norm_num⟩
  | 14 => ⟨((-776100325/140737488355328), (-503365931/281474976710656)), (163/140737488355328), by norm_num⟩
  | 15 => ⟨((319861207/281474976710656), (414913457/1125899906842624)), (271/1125899906842624), by norm_num⟩
  | 16 => ⟨((-494352285/2251799813685248), (-160314389/2251799813685248)), (211/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-1841893810255/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777847662991215/633825300114114700748351602688), (-2177658014283/316912650057057350374175801344)), (46315/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888705309910309/39614081257132168796771975168), (-2449289242795/19807040628566084398385987584)), (26059/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888415187344455/2475880078570760549798248448), (-5203321878213/2475880078570760549798248448)), (110783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27657515217837/2417851639229258349412352), (-5201727229513/154742504910672534362390528)), (110819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774256288866529/4835703278458516698824704), (-4874925399189/9671406556917033397649408)), (103931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257877451278627/604462909807314587353088), (-4263866335275/604462909807314587353088)), (45489/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943155186885423/37778931862957161709568), (-1731402182659/18889465931478580854784)), (147909/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296427397056995/4722366482869645213696), (-2595715141075/2361183241434822606848)), (110995/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619917734668025/590295810358705651712), (-3566853578431/295147905179352825856)), (9545/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455389923278751/18446744073709551616), (-4455186569475/36893488147419103232)), (191053/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455124978582215/2305843009213693952), (-10014879221011/9223372036854775808)), (107573/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795872532609777/576460752303423488), (-10003274346431/1152921504606846976)), (215409/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596308153432405/72057594037927936), (-2184955254933/36028797018963968)), (47195/36028797018963968), by norm_num⟩
  | 4 => ⟨((372170808727991/9007199254740992), (-817729506035/2251799813685248)), (283765/36028797018963968), by norm_num⟩
  | 3 => ⟨((371387990380333/2251799813685248), (-4077262639777/2251799813685248)), (88937/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110248971774777/2251799813685248), (-16240870159017/2251799813685248)), (357315/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102416471368959/1125899906842624), (-3023913219483/140737488355328)), (134975/281474976710656), by norm_num⟩
  | 0 => ⟨((269727000347627/281474976710656), (-47705324395121/1125899906842624)), (1095583/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((269727000347627/281474976710656), (-47705324395121/1125899906842624)), (4179317478660201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063712183344565/2251799813685248), (-22857118952591/281474976710656)), (2192555/1125899906842624), by norm_num⟩
  | 2 => ⟨((58640194241077/70368744177664), (-335166666748549/2251799813685248)), (1093731/281474976710656), by norm_num⟩
  | 3 => ⟨((1513839641761131/2251799813685248), (-558607054053631/2251799813685248)), (8593849/1125899906842624), by norm_num⟩
  | 4 => ⟨((27473421039939/70368744177664), (-751080533406591/2251799813685248)), (31637439/2251799813685248), by norm_num⟩
  | 5 => ⟨((92717757339651/2251799813685248), (-146618729453829/562949953421312)), (91617919/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1191424724923661/18014398509481984), (-386369259187747/18014398509481984)), (221071949/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-1781521695/33554432)), (1/16777216), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1807141459/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1085427634502545/18014398509481984), (524237316445589/18014398509481984)), (108725883/9007199254740992), by norm_num⟩
  | 1 => ⟨((811422365/4294967296), (-48987361/536870912)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-636052533/2147483648), (153599587/1073741824)), (259/4294967296), by norm_num⟩
  | 3 => ⟨((1329559359/4294967296), (-642147489/4294967296)), (273/4294967296), by norm_num⟩
  | 4 => ⟨((-260551605/1073741824), (251681217/2147483648)), (27/536870912), by norm_num⟩
  | 5 => ⟨((81695805/536870912), (-19728625/268435456)), (273/8589934592), by norm_num⟩
  | 6 => ⟨((-1366169195/17179869184), (329914611/8589934592)), (287/17179869184), by norm_num⟩
  | 7 => ⟨((611945087/17179869184), (-591111631/34359738368)), (259/34359738368), by norm_num⟩
  | 8 => ⟨((-239843785/17179869184), (463356775/68719476736)), (205/68719476736), by norm_num⟩
  | 9 => ⟨((668470045/137438953472), (-645712217/274877906944)), (9/8589934592), by norm_num⟩
  | 10 => ⟨((-52399599/34359738368), (50615673/68719476736)), (91/274877906944), by norm_num⟩
  | 11 => ⟨((955919357/2199023255552), (-461687709/2199023255552)), (209/2199023255552), by norm_num⟩
  | 12 => ⟨((-999093205/8796093022208), (241269857/4398046511104)), (55/2199023255552), by norm_num⟩
  | 13 => ⟨((963892605/35184372088832), (-232769305/17592186044416)), (107/17592186044416), by norm_num⟩
  | 14 => ⟨((-431754241/70368744177664), (52131915/17592186044416)), (193/140737488355328), by norm_num⟩
  | 15 => ⟨((1444013787/1125899906842624), (-697426423/1125899906842624)), (325/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1131924219/4503599627370496), (546694129/4503599627370496)), (257/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1753090843861/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444447394132045/158456325028528675187087900672), (1036267810269/158456325028528675187087900672)), (92609/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888640031371085/39614081257132168796771975168), (4662096815607/39614081257132168796771975168)), (104211/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944172959236369/1237940039285380274899124224), (4952109511419/2475880078570760549798248448)), (110755/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110625737860507/9671406556917033397649408), (4950570497359/154742504910672534362390528)), (110789/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387111959873347/2417851639229258349412352), (4639525095205/9671406556917033397649408)), (103901/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628910456082183/302231454903657293676544), (2028975112499/302231454903657293676544)), (45475/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943109348940391/37778931862957161709568), (3295553008891/37778931862957161709568)), (147861/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296358815124189/4722366482869645213696), (4940650392319/4722366482869645213696)), (27739/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25309745602379/9223372036854775808), (848630345091/73786976294838206464)), (76331/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821442598493713/73786976294838206464), (8479779732911/73786976294838206464)), (190973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227546095887343/1152921504606846976), (2382696974149/2305843009213693952)), (215045/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591614646950167/1152921504606846976), (9519591231617/1152921504606846976)), (841/4503599627370496), by norm_num⟩
  | 5 => ⟨((298125752289099/36028797018963968), (8317058060373/144115188075855872)), (188667/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488514920399949/36028797018963968), (6225224253213/18014398509481984)), (283565/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485344414349129/9007199254740992), (15519135494731/9007199254740992)), (355449/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220091346691941/4503599627370496), (30906765086063/4503599627370496)), (713879/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204244150009273/2251799813685248), (23016163022129/1125899906842624)), (1078299/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156721982998573/2251799813685248), (45379511891649/1125899906842624)), (2186649/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156721982998573/2251799813685248), (45379511891649/1125899906842624)), (8341403969771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062000575420697/2251799813685248), (173853804018735/2251799813685248)), (4364911/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874776435368153/2251799813685248), (318400100885537/2251799813685248)), (4334003/1125899906842624), by norm_num⟩
  | 3 => ⟨((189482210942049/281474976710656), (530179461363509/2251799813685248)), (16884687/2251799813685248), by norm_num⟩
  | 4 => ⟨((447804963690563/1125899906842624), (178452055861595/562949953421312)), (1917727/140737488355328), by norm_num⟩
  | 5 => ⟨((129938265553497/2251799813685248), (1135613791740409/4503599627370496)), (43860733/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1085427634502545/18014398509481984), (524237316445589/18014398509481984)), (108725883/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1807141459/33554432)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-457917671/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-441578649108385/18014398509481984), (1074772949841617/18014398509481984)), (25804287/2251799813685248), by norm_num⟩
  | 1 => ⟨((83646817/1073741824), (-12724423/67108864)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-265834087/2147483648), (161755605/536870912)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((563223359/4294967296), (-1370848053/4294967296)), (135/2147483648), by norm_num⟩
  | 4 => ⟨((-223744269/2147483648), (544578613/2147483648)), (27/536870912), by norm_num⟩
  | 5 => ⟨((568857065/8589934592), (-1384560117/8589934592)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((-301309729/8589934592), (1466735527/17179869184)), (37/2147483648), by norm_num⟩
  | 7 => ⟨((68398467/4294967296), (-1331818417/34359738368)), (271/34359738368), by norm_num⟩
  | 8 => ⟨((-108687005/17179869184), (1058147655/68719476736)), (217/68719476736), by norm_num⟩
  | 9 => ⟨((614067827/274877906944), (-373650023/68719476736)), (309/274877906944), by norm_num⟩
  | 10 => ⟨((-195154061/274877906944), (949983909/549755813888)), (99/274877906944), by norm_num⟩
  | 11 => ⟨((451061899/2199023255552), (-548927273/1099511627776)), (231/2199023255552), by norm_num⟩
  | 12 => ⟨((-477832999/8796093022208), (1163013615/8796093022208)), (247/8796093022208), by norm_num⟩
  | 13 => ⟨((467255075/35184372088832), (-1137267653/35184372088832)), (61/8796093022208), by norm_num⟩
  | 14 => ⟨((-212137397/70368744177664), (129082065/17592186044416)), (223/140737488355328), by norm_num⟩
  | 15 => ⟨((89891209/140737488355328), (-437578401/281474976710656)), (191/562949953421312), by norm_num⟩
  | 16 => ⟨((-285679101/2251799813685248), (1390647713/4503599627370496)), (305/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (319242033197/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777737375780353/633825300114114700748351602688), (3019126421351/633825300114114700748351602688)), (46249/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888581557049589/39614081257132168796771975168), (1697854102715/19807040628566084398385987584)), (6505/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472071031314305/618970019642690137449562112), (225433173727/154742504910672534362390528)), (55303/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769950389875807/154742504910672534362390528), (901448971977/38685626227668133590597632)), (110631/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774195331340499/4835703278458516698824704), (3379228242665/9671406556917033397649408)), (103743/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257771282681031/604462909807314587353088), (2955619782693/604462909807314587353088)), (45401/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943069399817109/37778931862957161709568), (4800623907769/75557863725914323419136)), (147603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648149773316471/2361183241434822606848), (3598492975199/4722366482869645213696)), (55373/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619743287638501/590295810358705651712), (1236180104735/147573952589676412928)), (76173/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821343652247259/73786976294838206464), (3088046340395/36893488147419103232)), (190539/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227532454757803/1152921504606846976), (6941498825271/9223372036854775808)), (107251/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591508243704951/1152921504606846976), (1733312508577/288230376151711744)), (214685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149051620561723/18014398509481984), (1514331223799/36028797018963968)), (23507/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488385948950055/36028797018963968), (2266869265059/9007199254740992)), (282495/36028797018963968), by norm_num⟩
  | 3 => ⟨((742596910256683/4503599627370496), (353187972089/281474976710656)), (176921/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109910917016029/2251799813685248), (11253641656443/2251799813685248)), (709859/4503599627370496), by norm_num⟩
  | 1 => ⟨((275489802282367/281474976710656), (33519919785351/2251799813685248)), (1070241/2251799813685248), by norm_num⟩
  | 0 => ⟨((269547598011095/281474976710656), (16520244665911/562949953421312)), (1081201/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269547598011095/281474976710656), (16520244665911/562949953421312)), (4124454502585982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1031532945782423/1125899906842624), (31640413086023/562949953421312)), (2134229/1125899906842624), by norm_num⟩
  | 2 => ⟨((941518645512881/1125899906842624), (1811780087979/17592186044416)), (2075303/562949953421312), by norm_num⟩
  | 3 => ⟨((387695230132601/562949953421312), (387859639522775/2251799813685248)), (15593401/2251799813685248), by norm_num⟩
  | 4 => ⟨((500596533894535/1125899906842624), (133556572205089/562949953421312)), (13424817/1125899906842624), by norm_num⟩
  | 5 => ⟨((636814895324739/4503599627370496), (950108715254355/4503599627370496)), (18307777/1125899906842624), by norm_num⟩
  | 6 => ⟨((-441578649108385/18014398509481984), (1074772949841617/18014398509481984)), (25804287/2251799813685248), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-457917671/8388608)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1855198433/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((343642110055097/18014398509481984), (1067818170338785/18014398509481984)), (163475827/18014398509481984), by norm_num⟩
  | 1 => ⟨((-32965579/536870912), (-204871541/1073741824)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((424448421/4294967296), (1318912101/4294967296)), (103/2147483648), by norm_num⟩
  | 3 => ⟨((-455415587/4294967296), (-1415138093/4294967296)), (223/4294967296), by norm_num⟩
  | 4 => ⟨((91620389/1073741824), (1138788449/4294967296)), (181/4294967296), by norm_num⟩
  | 5 => ⟨((-58982931/1073741824), (-1466247443/8589934592)), (59/2147483648), by norm_num⟩
  | 6 => ⟨((506289949/17179869184), (49163213/536870912)), (255/17179869184), by norm_num⟩
  | 7 => ⟨((-58203017/4294967296), (-1446859683/34359738368)), (237/34359738368), by norm_num⟩
  | 8 => ⟨((374696569/68719476736), (582157707/34359738368)), (3/1073741824), by norm_num⟩
  | 9 => ⟨((-134011303/68719476736), (-416420749/68719476736)), (139/137438953472), by norm_num⟩
  | 10 => ⟨((345092595/549755813888), (536162673/274877906944)), (181/549755813888), by norm_num⟩
  | 11 => ⟨((-201965493/1099511627776), (-1255157139/2199023255552)), (107/1099511627776), by norm_num⟩
  | 12 => ⟨((433401229/8796093022208), (1346731657/8796093022208)), (29/1099511627776), by norm_num⟩
  | 13 => ⟨((-429250689/35184372088832), (-666917227/17592186044416)), (29/4398046511104), by norm_num⟩
  | 14 => ⟨((197386381/70368744177664), (76668705/8796093022208)), (215/140737488355328), by norm_num⟩
  | 15 => ⟨((-338859867/562949953421312), (-526479021/281474976710656)), (93/281474976710656), by norm_num⟩
  | 16 => ⟨((272686959/2251799813685248), (847335297/2251799813685248)), (19/281474976710656), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (1640568995365/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777686032030053/633825300114114700748351602688), (1939279823497/633825300114114700748351602688)), (92391/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888523966430831/39614081257132168796771975168), (2181167506381/39614081257132168796771975168)), (103953/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888223163862795/2475880078570760549798248448), (1158417172089/1237940039285380274899124224)), (863/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1769889685409339/154742504910672534362390528), (2316096557297/154742504910672534362390528)), (6905/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((96770876563199/604462909807314587353088), (1085278466933/4835703278458516698824704)), (12949/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314430499310377/151115727451828646838272), (1898454077341/604462909807314587353088)), (90661/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943029610625345/37778931862957161709568), (1541760020965/37778931862957161709568)), (147355/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296240308972223/4722366482869645213696), (2311356417373/4722366482869645213696)), (6909/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619662559833777/590295810358705651712), (3176030588515/590295810358705651712)), (38011/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910621913375351/36893488147419103232), (3966913934001/73786976294838206464)), (190123/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820148822461983/9223372036854775808), (4458486200711/9223372036854775808)), (106991/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198924910506785/144115188075855872), (4453127135885/1152921504606846976)), (53525/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192319707040497/144115188075855872), (3890465404839/144115188075855872)), (93735/72057594037927936), by norm_num⟩
  | 4 => ⟨((186031276628111/4503599627370496), (2911838337023/18014398509481984)), (281471/36028797018963968), by norm_num⟩
  | 3 => ⟨((742515690810101/4503599627370496), (3629301905297/4503599627370496)), (352305/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219518521949609/4503599627370496), (903400816005/281474976710656)), (706011/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101758460244271/1125899906842624), (10762633424897/1125899906842624)), (132817/281474976710656), by norm_num⟩
  | 0 => ⟨((2155789020639207/2251799813685248), (10607227857265/562949953421312)), (2139235/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155789020639207/2251799813685248), (10607227857265/562949953421312)), (8160533913619231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1031536209557759/1125899906842624), (81239709551931/2251799813685248)), (522083/281474976710656), by norm_num⟩
  | 2 => ⟨((58975989593411/70368744177664), (148861726601929/2251799813685248)), (3977295/1125899906842624), by norm_num⟩
  | 3 => ⟨((196480806693419/281474976710656), (124760896922745/1125899906842624)), (14385195/2251799813685248), by norm_num⟩
  | 4 => ⟨((1069562282263411/2251799813685248), (43544051335643/281474976710656)), (23270931/2251799813685248), by norm_num⟩
  | 5 => ⟨((454131875931181/2251799813685248), (82730400175893/562949953421312)), (29306509/2251799813685248), by norm_num⟩
  | 6 => ⟨((343642110055097/18014398509481984), (1067818170338785/18014398509481984)), (163475827/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1855198433/33554432)), (1/16777216), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-94291587/33554432), (-1877803283/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((903649421082679/18014398509481984), (149880436428281/4503599627370496)), (54944295/9007199254740992), by norm_num⟩
  | 1 => ⟨((-701946509/4294967296), (-465702945/4294967296)), (87/4294967296), by norm_num⟩
  | 2 => ⟨((571752373/2147483648), (758652577/4294967296)), (9/268435456), by norm_num⟩
  | 3 => ⟨((-155235369/536870912), (-102990139/536870912)), (159/4294967296), by norm_num⟩
  | 4 => ⟨((1011543637/4294967296), (671103631/4294967296)), (131/4294967296), by norm_num⟩
  | 5 => ⟨((-164785341/1073741824), (-437304083/4294967296)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((178962183/2147483648), (237463153/4294967296)), (3/268435456), by norm_num⟩
  | 7 => ⟨((-333186325/8589934592), (-110525411/4294967296)), (91/17179869184), by norm_num⟩
  | 8 => ⟨((271388303/17179869184), (360102459/34359738368)), (75/34359738368), by norm_num⟩
  | 9 => ⟨((-392981907/68719476736), (-521443811/137438953472)), (55/68719476736), by norm_num⟩
  | 10 => ⟨((1024298393/549755813888), (339782855/274877906944)), (145/549755813888), by norm_num⟩
  | 11 => ⟨((-1213550199/2199023255552), (-402561943/1099511627776)), (87/1099511627776), by norm_num⟩
  | 12 => ⟨((164744321/1099511627776), (54649403/549755813888)), (3/137438953472), by norm_num⟩
  | 13 => ⟨((-165154739/4398046511104), (-438284383/17592186044416)), (49/8796093022208), by norm_num⟩
  | 14 => ⟨((1229920191/140737488355328), (815984475/140737488355328)), (23/17592186044416), by norm_num⟩
  | 15 => ⟨((-1068586325/562949953421312), (-354474159/281474976710656)), (81/281474976710656), by norm_num⟩
  | 16 => ⟨((108798669/281474976710656), (577455515/2251799813685248)), (67/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (763029450973/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777635527032857/633825300114114700748351602688), (450954795721/316912650057057350374175801344)), (46145/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888467248362591/39614081257132168796771975168), (1014403536955/39614081257132168796771975168)), (12979/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944081517231777/1237940039285380274899124224), (1077495001989/2475880078570760549798248448)), (13791/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884914853039107/77371252455336267181195264), (134643480119/19342813113834066795298816)), (110335/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774138976854727/4835703278458516698824704), (1009457398329/9671406556917033397649408)), (103447/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257673094031573/604462909807314587353088), (441453348311/302231454903657293676544)), (22631/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942990025846779/37778931862957161709568), (1434032767083/75557863725914323419136)), (147117/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81011324524501/295147905179352825856), (537460330029/2361183241434822606848)), (110351/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809790848713093/295147905179352825856), (1477035243809/590295810358705651712)), (151753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56910730690293/2305843009213693952), (1844824280521/73786976294838206464)), (47431/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820036691469779/9223372036854775808), (2073408358951/9223372036854775808)), (213483/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591288237227653/1152921504606846976), (2070887634331/1152921504606846976)), (106769/576460752303423488), by norm_num⟩
  | 5 => ⟨((149027969682589/18014398509481984), (1809194944939/144115188075855872)), (186909/144115188075855872), by norm_num⟩
  | 4 => ⟨((372027178307135/9007199254740992), (2708139131673/36028797018963968)), (35061/4503599627370496), by norm_num⟩
  | 3 => ⟨((371214682861815/2251799813685248), (1687651768145/4503599627370496)), (175415/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219185821847139/4503599627370496), (6721087208441/4503599627370496)), (351161/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203049114902717/2251799813685248), (5004074814755/1125899906842624)), (65947/140737488355328), by norm_num⟩
  | 0 => ⟨((538744215102781/562949953421312), (19724277648185/2251799813685248)), (1058529/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538744215102781/562949953421312), (19724277648185/2251799813685248)), (4037967686179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1031072165819911/1125899906842624), (4719043147379/281474976710656)), (4089147/2251799813685248), by norm_num⟩
  | 2 => ⟨((471957362629697/562949953421312), (69145386853587/2251799813685248)), (7626599/2251799813685248), by norm_num⟩
  | 3 => ⟨((395141580536211/562949953421312), (57969050746161/1125899906842624)), (13256119/2251799813685248), by norm_num⟩
  | 4 => ⟨((1103449889381751/2251799813685248), (40689198382221/562949953421312)), (19974303/2251799813685248), by norm_num⟩
  | 5 => ⟨((132239983911741/562949953421312), (39877871186439/562949953421312)), (44926901/4503599627370496), by norm_num⟩
  | 6 => ⟨((903649421082679/18014398509481984), (149880436428281/4503599627370496)), (54944295/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-1877803283/33554432)), (1/16777216), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1899554913/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((523829894899237/9007199254740992), (-131086494228921/36028797018963968)), (139120517/36028797018963968), by norm_num⟩
  | 1 => ⟨((-823239269/4294967296), (103006291/8589934592)), (7/536870912), by norm_num⟩
  | 2 => ⟨((678315583/2147483648), (-84872983/4294967296)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-745205835/2147483648), (46621251/2147483648)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((38376201/134217728), (-76828019/4294967296)), (11/536870912), by norm_num⟩
  | 5 => ⟨((-1618965735/8589934592), (101285047/8589934592)), (59/4294967296), by norm_num⟩
  | 6 => ⟨((1778615651/17179869184), (-111272997/17179869184)), (33/4294967296), by norm_num⟩
  | 7 => ⟨((-1674864867/34359738368), (13097773/4294967296)), (127/34359738368), by norm_num⟩
  | 8 => ⟨((172502543/8589934592), (-43168123/34359738368)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((-505369103/68719476736), (31616687/68719476736)), (5/8589934592), by norm_num⟩
  | 10 => ⟨((41640353/17179869184), (-41681377/274877906944)), (107/549755813888), by norm_num⟩
  | 11 => ⟨((-1596972341/2199023255552), (99909105/2199023255552)), (65/1099511627776), by norm_num⟩
  | 12 => ⟨((877226719/4398046511104), (-54880685/4398046511104)), (145/8796093022208), by norm_num⟩
  | 13 => ⟨((-1779197637/35184372088832), (55654703/17592186044416)), (149/35184372088832), by norm_num⟩
  | 14 => ⟨((209426613/17592186044416), (-52408235/70368744177664)), (71/70368744177664), by norm_num⟩
  | 15 => ⟨((-368125841/140737488355328), (46061065/281474976710656)), (127/562949953421312), by norm_num⟩
  | 16 => ⟨((606641359/1125899906842624), (-37952439/1125899906842624)), (53/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-81387365771/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55549557532133/19807040628566084398385987584), (-24048907147/158456325028528675187087900672)), (46105/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944205694342633/19807040628566084398385987584), (-108193721695/39614081257132168796771975168)), (103737/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888103732413031/2475880078570760549798248448), (-28730630101/618970019642690137449562112)), (55111/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769770458934499/154742504910672534362390528), (-14360633643/19342813113834066795298816)), (55111/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548222467809379/9671406556917033397649408), (-26916244407/2417851639229258349412352)), (103335/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257624602119609/604462909807314587353088), (-47083550087/302231454903657293676544)), (90419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885901361457647/75557863725914323419136), (-152947037977/75557863725914323419136)), (36733/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648061135048611/2361183241434822606848), (-57322566209/2361183241434822606848)), (110201/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619500834081829/590295810358705651712), (-78765636017/295147905179352825856)), (18941/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910521267401025/36893488147419103232), (-98377773833/36893488147419103232)), (94707/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819923556599821/9223372036854775808), (-221132214819/9223372036854775808)), (26637/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591175499482141/1152921504606846976), (-220860323255/1152921504606846976)), (213103/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192125557619757/144115188075855872), (-96473678179/72057594037927936)), (186473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487962302149215/36028797018963968), (-144405654267/18014398509481984)), (139863/18014398509481984), by norm_num⟩
  | 3 => ⟨((742338633377115/4503599627370496), (-179974822937/4503599627370496)), (174843/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218827515860761/4503599627370496), (-358357960147/2251799813685248)), (349731/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202523130547727/2251799813685248), (-533575341371/1125899906842624)), (131179/281474976710656), by norm_num⟩
  | 0 => ⟨((2153970289867049/2251799813685248), (-2102819068529/2251799813685248)), (2099891/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153970289867049/2251799813685248), (-2102819068529/2251799813685248)), (8010448464400481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257548626191423/281474976710656), (-4022924037075/2251799813685248)), (4021245/2251799813685248), by norm_num⟩
  | 2 => ⟨((942620800676843/1125899906842624), (-920240380805/281474976710656)), (1843305/562949953421312), by norm_num⟩
  | 3 => ⟨((1578329332813619/2251799813685248), (-1540878934793/281474976710656)), (774635/140737488355328), by norm_num⟩
  | 4 => ⟨((2212427154470845/4503599627370496), (-34561003603505/4503599627370496)), (35020609/4503599627370496), by norm_num⟩
  | 5 => ⟨((2173212477027899/9007199254740992), (-16978352692245/2251799813685248)), (69891555/9007199254740992), by norm_num⟩
  | 6 => ⟨((523829894899237/9007199254740992), (-131086494228921/36028797018963968)), (139120517/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1899554913/33554432)), (1/16777216), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile006Terms3

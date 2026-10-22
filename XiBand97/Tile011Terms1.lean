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
namespace Reinmann.XiBand97.Tile011Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25029/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25029/1280))
  have he : value ((69/80), (25029/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-360410867/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((22214706702119/281474976710656), (1152148716968489/9007199254740992)), (87175775/4503599627370496), by norm_num⟩
  | 1 => ⟨((-744792169/4294967296), (-603563661/2147483648)), (93/2147483648), by norm_num⟩
  | 2 => ⟨((409118915/2147483648), (663082455/2147483648)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((-299642045/2147483648), (-971294045/4294967296)), (77/2147483648), by norm_num⟩
  | 4 => ⟨((329190433/4294967296), (533537787/4294967296)), (171/8589934592), by norm_num⟩
  | 5 => ⟨((-72330531/2147483648), (-937841871/17179869184)), (19/2147483648), by norm_num⟩
  | 6 => ⟨((105950947/8589934592), (343441535/17179869184)), (113/34359738368), by norm_num⟩
  | 7 => ⟨((-532109771/137438953472), (-862420779/137438953472)), (9/8589934592), by norm_num⟩
  | 8 => ⟨((584582333/549755813888), (473733033/274877906944)), (161/549755813888), by norm_num⟩
  | 9 => ⟨((-71358815/274877906944), (-925242545/2199023255552)), (159/2199023255552), by norm_num⟩
  | 10 => ⟨((501732295/8796093022208), (101648283/1099511627776)), (71/4398046511104), by norm_num⟩
  | 11 => ⟨((-801758931/70368744177664), (-1299456615/70368744177664)), (229/70368744177664), by norm_num⟩
  | 12 => ⟨((293607405/140737488355328), (951732671/281474976710656)), (85/140737488355328), by norm_num⟩
  | 13 => ⟨((-793995577/2251799813685248), (-643437051/1125899906842624)), (233/2251799813685248), by norm_num⟩
  | 14 => ⟨((498453313/9007199254740992), (403935915/4503599627370496)), (37/2251799813685248), by norm_num⟩
  | 15 => ⟨((-36507129/4503599627370496), (-946707115/72057594037927936)), (175/72057594037927936), by norm_num⟩
  | 16 => ⟨((641714889/576460752303423488), (1040064071/576460752303423488)), (195/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (1326024465179/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889522270405961/316912650057057350374175801344), (1569745932907/633825300114114700748351602688)), (92355/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890052014300649/39614081257132168796771975168), (882834865849/19807040628566084398385987584)), (103909/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889846379148169/2475880078570760549798248448), (937830665423/1237940039285380274899124224)), (110415/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771512523238335/154742504910672534362390528), (1875253345545/154742504910672534362390528)), (27607/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549855034512475/9671406556917033397649408), (1757616640725/9671406556917033397649408)), (25885/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259052479686139/604462909807314587353088), (1537481317775/604462909807314587353088)), (90611/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888220503794449/75557863725914323419136), (2497595082651/75557863725914323419136)), (36817/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297860613580487/4722366482869645213696), (468121508033/1180591620717411303424)), (55237/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621889410934547/590295810358705651712), (321689324793/73786976294838206464)), (151939/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114001611855103/4611686018427387904), (1607581797203/36893488147419103232)), (94989/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911638165264929/4611686018427387904), (1807341107999/4611686018427387904)), (213801/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398631010860117/288230376151711744), (3611713348893/1152921504606846976)), (26737/144115188075855872), by norm_num⟩
  | 5 => ⟨((298762695360955/36028797018963968), (1578456091519/72057594037927936)), (93633/72057594037927936), by norm_num⟩
  | 4 => ⟨((373085162507443/9007199254740992), (295543857461/2251799813685248)), (281111/36028797018963968), by norm_num⟩
  | 3 => ⟨((93133352171643/562949953421312), (2949613699369/4503599627370496)), (87941/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229690698503161/4503599627370496), (5881786171825/2251799813685248)), (704651/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218694535039665/2251799813685248), (4389596445689/562949953421312)), (264949/562949953421312), by norm_num⟩
  | 0 => ⟨((546455673198349/562949953421312), (8692569482789/562949953421312)), (2130913/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546455673198349/562949953421312), (8692569482789/562949953421312)), (8128788002974700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1060620896021361/1125899906842624), (16875759131597/562949953421312)), (1050691/562949953421312), by norm_num⟩
  | 2 => ⟨((998114941889913/1125899906842624), (127178500770207/2251799813685248)), (8170157/2251799813685248), by norm_num⟩
  | 3 => ⟨((27538800252951/35184372088832), (56372134474137/562949953421312)), (15408635/2251799813685248), by norm_num⟩
  | 4 => ⟨((339228867954313/562949953421312), (352979657490267/2251799813685248)), (27206621/2251799813685248), by norm_num⟩
  | 5 => ⟨((762334621675671/2251799813685248), (106351274117355/562949953421312)), (20659239/1125899906842624), by norm_num⟩
  | 6 => ⟨((22214706702119/281474976710656), (1152148716968489/9007199254740992)), (87175775/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-360410867/8388608)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-188846579/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((311702856557173/4503599627370496), (-1067503161933447/9007199254740992)), (161362963/9007199254740992), by norm_num⟩
  | 1 => ⟨((-684473373/4294967296), (586036889/2147483648)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((788029093/4294967296), (-1349399805/4294967296)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-604834681/4294967296), (1035702625/4294967296)), (163/4294967296), by norm_num⟩
  | 4 => ⟨((174085415/2147483648), (-1192396713/8589934592)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((-320677185/8589934592), (1098237959/17179869184)), (89/8589934592), by norm_num⟩
  | 6 => ⟨((492257671/34359738368), (-52683049/2147483648)), (139/34359738368), by norm_num⟩
  | 7 => ⟨((-323847193/68719476736), (554547215/68719476736)), (185/137438953472), by norm_num⟩
  | 8 => ⟨((745685719/549755813888), (-1276892151/549755813888)), (215/549755813888), by norm_num⟩
  | 9 => ⟨((-381556627/1099511627776), (319027/536870912)), (223/2199023255552), by norm_num⟩
  | 10 => ⟨((702853281/8796093022208), (-1203547037/8796093022208)), (13/549755813888), by norm_num⟩
  | 11 => ⟨((-4597669/274877906944), (1007734351/35184372088832)), (177/35184372088832), by norm_num⟩
  | 12 => ⟨((451691695/140737488355328), (-386732349/70368744177664)), (69/70368744177664), by norm_num⟩
  | 13 => ⟨((-640036039/1125899906842624), (547990241/562949953421312)), (99/562949953421312), by norm_num⟩
  | 14 => ⟨((421067841/4503599627370496), (-360512617/2251799813685248)), (33/1125899906842624), by norm_num⟩
  | 15 => ⟨((-258545209/18014398509481984), (442725855/18014398509481984)), (41/9007199254740992), by norm_num⟩
  | 16 => ⟨((74415293/36028797018963968), (-509706977/144115188075855872)), (191/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-1357628603997/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778904358156811/633825300114114700748351602688), (-1606917907139/633825300114114700748351602688)), (92359/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889894332325403/39614081257132168796771975168), (-1807467430119/39614081257132168796771975168)), (103913/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236209858819781/309485009821345068724781056), (-960022507283/1237940039285380274899124224)), (27605/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885672523358579/77371252455336267181195264), (-959803689521/77371252455336267181195264)), (110433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549698059341743/9671406556917033397649408), (-1799167058477/9671406556917033397649408)), (103545/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314728790118453/151115727451828646838272), (-786903230605/302231454903657293676544)), (11327/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887997423928439/75557863725914323419136), (-639141116427/18889465931478580854784)), (147277/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648846679770449/2361183241434822606848), (-1916661501417/4722366482869645213696)), (110481/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621659527379319/590295810358705651712), (-2572433727/576460752303423488)), (151949/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911869285660439/36893488147419103232), (-3290860033945/73786976294838206464)), (23749/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911476698461287/4611686018427387904), (-57807318097/144115188075855872)), (213819/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594201343545011/1152921504606846976), (-3696484330975/1152921504606846976)), (53479/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194768681825051/144115188075855872), (-1615422561041/72057594037927936)), (93643/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491918025840819/36028797018963968), (-4839118748303/36028797018963968)), (281147/36028797018963968), by norm_num⟩
  | 3 => ⟨((186200784114061/1125899906842624), (-377275417445/562949953421312)), (175909/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228638726975357/4503599627370496), (-12035413504207/4503599627370496)), (704787/4503599627370496), by norm_num⟩
  | 1 => ⟨((69285107729697/70368744177664), (-8979942052715/1125899906842624)), (530035/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182707931251445/2251799813685248), (-35548400778683/2251799813685248)), (2131743/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182707931251445/2251799813685248), (-35548400778683/2251799813685248)), (8131954201705168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((528793700421697/562949953421312), (-68915341276231/2251799813685248)), (4199977/2251799813685248), by norm_num⟩
  | 2 => ⟨((248091276268543/281474976710656), (-64733992973633/1125899906842624)), (509211/140737488355328), by norm_num⟩
  | 3 => ⟨((1741891985180931/2251799813685248), (-228225458937281/2251799813685248)), (15299023/2251799813685248), by norm_num⟩
  | 4 => ⟨((1324318800368843/2251799813685248), (-44136261061155/281474976710656)), (26770473/2251799813685248), by norm_num⟩
  | 5 => ⟨((723486903462703/2251799813685248), (-415315641797597/2251799813685248)), (39883679/2251799813685248), by norm_num⟩
  | 6 => ⟨((311702856557173/4503599627370496), (-1067503161933447/9007199254740992)), (161362963/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-188846579/4194304)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-98331723/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1107171190737915/9007199254740992), (-265868004583211/9007199254740992)), (97958765/4503599627370496), by norm_num⟩
  | 1 => ⟨((158243213/536870912), (303994957/4294967296)), (113/2147483648), by norm_num⟩
  | 2 => ⟨((-758901305/2147483648), (-364474035/4294967296)), (273/4294967296), by norm_num⟩
  | 3 => ⟨((1213177235/4294967296), (145661761/2147483648)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-727267989/4294967296), (-21830103/536870912)), (133/4294967296), by norm_num⟩
  | 5 => ⟨((697564989/8589934592), (335016325/17179869184)), (257/17179869184), by norm_num⟩
  | 6 => ⟨((-1115125193/34359738368), (-267778021/34359738368)), (207/34359738368), by norm_num⟩
  | 7 => ⟨((381993347/34359738368), (91729093/34359738368)), (143/68719476736), by norm_num⟩
  | 8 => ⟨((-915980041/274877906944), (-109978379/137438953472)), (173/274877906944), by norm_num⟩
  | 9 => ⟨((488094269/549755813888), (234414787/1099511627776)), (93/549755813888), by norm_num⟩
  | 10 => ⟨((-58519947/274877906944), (-56210211/1099511627776)), (45/1099511627776), by norm_num⟩
  | 11 => ⟨((816434643/17592186044416), (392105307/35184372088832)), (79/8796093022208), by norm_num⟩
  | 12 => ⟨((-1305149847/140737488355328), (-156704577/70368744177664)), (255/140737488355328), by norm_num⟩
  | 13 => ⟨((481478869/281474976710656), (28904705/70368744177664)), (95/281474976710656), by norm_num⟩
  | 14 => ⟨((-1319469605/4503599627370496), (-79211949/1125899906842624)), (263/4503599627370496), by norm_num⟩
  | 15 => ⟨((843719981/18014398509481984), (405209511/36028797018963968)), (339/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1011576077/144115188075855872), (-242912493/144115188075855872)), (205/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-3785288121579/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778768263010405/633825300114114700748351602688), (-4479739263753/633825300114114700748351602688)), (92641/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889740722561921/39614081257132168796771975168), (-5038766862519/39614081257132168796771975168)), (52125/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118094687736367/154742504910672534362390528), (-5352557059965/2475880078570760549798248448)), (55399/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110698777628619/9671406556917033397649408), (-5351282746203/154742504910672534362390528)), (110835/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549542958987411/9671406556917033397649408), (-5015473766547/9671406556917033397649408)), (103947/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314694666188939/151115727451828646838272), (-4387185906377/604462909807314587353088)), (90993/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943887075831195/37778931862957161709568), (-7126639382915/75557863725914323419136)), (147937/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297524623185437/4722366482869645213696), (-1335689848977/1180591620717411303424)), (55509/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405356358422009/147573952589676412928), (-7342687114475/590295810358705651712)), (152753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911721418213545/36893488147419103232), (-9172949493411/73786976294838206464)), (191099/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822616414754681/9223372036854775808), (-5156066090527/4611686018427387904)), (107601/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593859020655827/1152921504606846976), (-10302840077021/1152921504606846976)), (215473/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298615788609955/36028797018963968), (-9004535441131/144115188075855872)), (47211/36028797018963968), by norm_num⟩
  | 4 => ⟨((46607743082687/1125899906842624), (-13485913917483/36028797018963968)), (283875/36028797018963968), by norm_num⟩
  | 3 => ⟨((744498808101581/4503599627370496), (-8410429412105/4503599627370496)), (355911/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113679585919493/2251799813685248), (-16766103889071/2251799813685248)), (357517/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107524781493317/1125899906842624), (-25012428439855/1125899906842624)), (540299/1125899906842624), by norm_num⟩
  | 0 => ⟨((544487063185693/562949953421312), (-49478914615517/1125899906842624)), (1096751/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544487063185693/562949953421312), (-49478914615517/1125899906842624)), (4183773045066451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051084983418699/1125899906842624), (-95712340839137/1125899906842624)), (2217959/1125899906842624), by norm_num⟩
  | 2 => ⟨((243276241413821/281474976710656), (-178704702918021/1125899906842624)), (4518253/1125899906842624), by norm_num⟩
  | 3 => ⟨((1625362783631263/2251799813685248), (-154452836116795/562949953421312)), (9244459/1125899906842624), by norm_num⟩
  | 4 => ⟨((62730746182605/140737488355328), (-891879962418817/2251799813685248)), (36836191/2251799813685248), by norm_num⟩
  | 5 => ⟨((94123660373389/2251799813685248), (-99384137449203/281474976710656)), (62017635/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1107171190737915/9007199254740992), (-265868004583211/9007199254740992)), (97958765/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-98331723/2097152)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1630397491/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-55383628204089/4503599627370496), (1050497418922531/9007199254740992)), (175141277/9007199254740992), by norm_num⟩
  | 1 => ⟨((32811915/1073741824), (-622365003/2147483648)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((-40767273/1073741824), (773259467/2147483648)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((67535245/2147483648), (-1280985061/4294967296)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-167818779/8589934592), (397891037/2147483648)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((5212675/536870912), (-790977667/8589934592)), (277/17179869184), by norm_num⟩
  | 6 => ⟨((-17270681/4294967296), (1310337109/34359738368)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((98093783/68719476736), (-1860608797/137438953472)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((-121876947/274877906944), (1155859793/274877906944)), (13/17179869184), by norm_num⟩
  | 9 => ⟨((33650315/274877906944), (-1276534971/1099511627776)), (29/137438953472), by norm_num⟩
  | 10 => ⟨((-66894313/2199023255552), (1268828095/4398046511104)), (233/4398046511104), by norm_num⟩
  | 11 => ⟨((60445863/8796093022208), (-1146516135/17592186044416)), (213/17592186044416), by norm_num⟩
  | 12 => ⟨((-200269769/140737488355328), (29676933/2199023255552)), (89/35184372088832), by norm_num⟩
  | 13 => ⟨((76561797/281474976710656), (-181524697/70368744177664)), (137/281474976710656), by norm_num⟩
  | 14 => ⟨((-27178417/562949953421312), (515510773/1125899906842624)), (197/2251799813685248), by norm_num⟩
  | 15 => ⟨((144076435/18014398509481984), (-1366395891/18014398509481984)), (263/18014398509481984), by norm_num⟩
  | 16 => ⟨((-89504123/72057594037927936), (848841559/72057594037927936)), (165/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (545745697619/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778659747356003/633825300114114700748351602688), (2583154097781/633825300114114700748351602688)), (92455/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944809535883731/19807040628566084398385987584), (2905500078939/39614081257132168796771975168)), (26007/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944693153180013/1237940039285380274899124224), (3086418449581/2475880078570760549798248448)), (27637/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885526185159753/77371252455336267181195264), (3085658849839/154742504910672534362390528)), (55285/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774711778058083/4835703278458516698824704), (2891998308205/9671406556917033397649408)), (51841/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629337425585729/302231454903657293676544), (1264845946847/302231454903657293676544)), (11343/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471901674621365/18889465931478580854784), (4109237408179/75557863725914323419136)), (147501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40543753773311/147573952589676412928), (1540302815735/2361183241434822606848)), (13833/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202657001014545/73786976294838206464), (4233684748921/590295810358705651712)), (76111/295147905179352825856), by norm_num⟩
  | 8 => ⟨((56976053100499/2305843009213693952), (2644442799565/36893488147419103232)), (5949/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1822384766779215/9223372036854775808), (5945571023211/9223372036854775808)), (214289/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796815952097979/576460752303423488), (5940043458135/1152921504606846976)), (214445/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298567378722125/36028797018963968), (5191325053203/144115188075855872)), (187815/144115188075855872), by norm_num⟩
  | 4 => ⟨((745583733768433/18014398509481984), (3887287735635/18014398509481984)), (141037/18014398509481984), by norm_num⟩
  | 3 => ⟨((186083115897391/1125899906842624), (2424132314763/2251799813685248)), (353209/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113373327828199/2251799813685248), (19328112603069/4503599627370496)), (708269/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214262112945849/2251799813685248), (1801889921195/140737488355328)), (266761/562949953421312), by norm_num⟩
  | 0 => ⟨((2176893679792465/2251799813685248), (7126920052535/281474976710656)), (1076359/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176893679792465/2251799813685248), (7126920052535/281474976710656)), (4105983738425826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2103035675292253/2251799813685248), (1722460753889/35184372088832)), (2135615/1125899906842624), by norm_num⟩
  | 2 => ⟨((30604732274401/35184372088832), (102954698340891/1125899906842624)), (4198153/1125899906842624), by norm_num⟩
  | 3 => ⟨((1684926969466369/2251799813685248), (89553992072373/562949953421312)), (16142419/2251799813685248), by norm_num⟩
  | 4 => ⟨((1203774951940037/2251799813685248), (134018961675969/562949953421312)), (29293253/2251799813685248), by norm_num⟩
  | 5 => ⟨((1031794047089605/4503599627370496), (1146309139347631/4503599627370496)), (90533609/4503599627370496), by norm_num⟩
  | 6 => ⟨((-55383628204089/4503599627370496), (1050497418922531/9007199254740992)), (175141277/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1630397491/33554432)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1682915131/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((979821557952757/9007199254740992), (108914641926793/9007199254740992)), (67693943/9007199254740992), by norm_num⟩
  | 1 => ⟨((-599191827/2147483648), (-66604743/2147483648)), (85/4294967296), by norm_num⟩
  | 2 => ⟨((384224173/1073741824), (170837793/4294967296)), (111/4294967296), by norm_num⟩
  | 3 => ⟨((-164252591/536870912), (-146063429/4294967296)), (97/4294967296), by norm_num⟩
  | 4 => ⟨((1685198311/8589934592), (187322649/8589934592)), (127/8589934592), by norm_num⟩
  | 5 => ⟨((-864489665/8589934592), (-192189243/17179869184)), (133/17179869184), by norm_num⟩
  | 6 => ⟨((1478248141/34359738368), (82159279/17179869184)), (29/8589934592), by norm_num⟩
  | 7 => ⟨((-135415415/8589934592), (-120419651/68719476736)), (87/68719476736), by norm_num⟩
  | 8 => ⟨((1389334727/274877906944), (154435153/274877906944)), (113/274877906944), by norm_num⟩
  | 9 => ⟨((-791905159/549755813888), (-88026299/549755813888)), (131/1099511627776), by norm_num⟩
  | 10 => ⟨((1624957303/4398046511104), (180626399/4398046511104)), (137/4398046511104), by norm_num⟩
  | 11 => ⟨((-1515612069/17592186044416), (-84235921/8796093022208)), (65/8796093022208), by norm_num⟩
  | 12 => ⟨((647911367/35184372088832), (144040581/70368744177664)), (113/70368744177664), by norm_num⟩
  | 13 => ⟨((-1022682981/281474976710656), (-56839507/140737488355328)), (91/281474976710656), by norm_num⟩
  | 14 => ⟨((374732865/562949953421312), (166617665/2251799813685248)), (135/2251799813685248), by norm_num⟩
  | 15 => ⟨((-256312219/2251799813685248), (-113964233/9007199254740992)), (47/4503599627370496), by norm_num⟩
  | 16 => ⟨((1314855723/72057594037927936), (146156243/72057594037927936)), (61/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (144203241921/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222319612143651/79228162514264337593543950336), (85309135499/316912650057057350374175801344)), (92217/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944751793976671/19807040628566084398385987584), (95954314965/19807040628566084398385987584)), (51873/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889263894337429/2475880078570760549798248448), (50964230389/618970019642690137449562112)), (110231/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770930283751921/154742504910672534362390528), (203805195309/154742504910672534362390528)), (13779/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549309445538747/9671406556917033397649408), (191012430033/9671406556917033397649408)), (6459/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((157321918719065/75557863725914323419136), (83540478303/302231454903657293676544)), (22607/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887445655668353/75557863725914323419136), (8481363265/2361183241434822606848)), (36737/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324319976057911/1180591620717411303424), (203462698967/4722366482869645213696)), (55107/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202636453567369/73786976294838206464), (34951876587/73786976294838206464)), (37887/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823029600246585/73786976294838206464), (174649806837/36893488147419103232)), (189441/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822157044007177/9223372036854775808), (196330483589/4611686018427387904)), (106565/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593406538018407/1152921504606846976), (98071237051/288230376151711744)), (213141/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194074964999863/144115188075855872), (171413397139/72057594037927936)), (186511/144115188075855872), by norm_num⟩
  | 4 => ⟨((372720229907517/9007199254740992), (513396333953/36028797018963968)), (139895/18014398509481984), by norm_num⟩
  | 3 => ⟨((23254936644343/140737488355328), (320135696357/4503599627370496)), (174891/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226076174201323/4503599627370496), (1276131593711/4503599627370496)), (349849/2251799813685248), by norm_num⟩
  | 1 => ⟨((276665581980431/281474976710656), (951603703103/1125899906842624)), (1049891/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175289191240841/2251799813685248), (1881341048341/1125899906842624)), (131325/140737488355328), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175289191240841/2251799813685248), (1881341048341/1125899906842624)), (500965118945074037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2101371924357963/2251799813685248), (908708852053/281474976710656)), (1016659/562949953421312), by norm_num⟩
  | 2 => ⟨((1960969660593163/2251799813685248), (13568064141507/2251799813685248)), (952025/281474976710656), by norm_num⟩
  | 3 => ⟨((853809893320249/1125899906842624), (23631374310253/2251799813685248)), (13356849/2251799813685248), by norm_num⟩
  | 4 => ⟨((1294700743892085/2251799813685248), (17920510567791/1125899906842624)), (5134573/562949953421312), by norm_num⟩
  | 5 => ⟨((1487668155276613/4503599627370496), (82428991145793/4503599627370496)), (48542603/4503599627370496), by norm_num⟩
  | 6 => ⟨((979821557952757/9007199254740992), (108914641926793/9007199254740992)), (67693943/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1682915131/33554432)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1731538869/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((425993078689103/18014398509481984), (-1799903546435611/18014398509481984)), (68972109/4503599627370496), by norm_num⟩
  | 1 => ⟨((-67008743/1073741824), (1132499849/4294967296)), (11/268435456), by norm_num⟩
  | 2 => ⟨((353679829/4294967296), (-1494366013/4294967296)), (235/4294967296), by norm_num⟩
  | 3 => ⟨((-311127115/4294967296), (657286263/2147483648)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((410541147/8589934592), (-867308065/4294967296)), (279/8589934592), by norm_num⟩
  | 5 => ⟨((-216688325/8589934592), (457775141/4294967296)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((381235275/34359738368), (-1610793121/34359738368)), (33/4294967296), by norm_num⟩
  | 7 => ⟨((-143728821/34359738368), (607282199/34359738368)), (201/68719476736), by norm_num⟩
  | 8 => ⟨((189654299/137438953472), (-801326269/137438953472)), (67/68719476736), by norm_num⟩
  | 9 => ⟨((-55612063/137438953472), (939887095/549755813888)), (159/549755813888), by norm_num⟩
  | 10 => ⟨((58705369/549755813888), (-992166371/2199023255552)), (85/1099511627776), by norm_num⟩
  | 11 => ⟨((-225348123/8796093022208), (238034903/2199023255552)), (165/8796093022208), by norm_num⟩
  | 12 => ⟨((396471077/70368744177664), (-1675167347/70368744177664)), (293/70368744177664), by norm_num⟩
  | 13 => ⟨((-80485377/70368744177664), (1360265435/281474976710656)), (15/17592186044416), by norm_num⟩
  | 14 => ⟨((121374585/562949953421312), (-1025662419/1125899906842624)), (183/1125899906842624), by norm_num⟩
  | 15 => ⟨((-341668787/9007199254740992), (721808513/4503599627370496)), (65/2251799813685248), by norm_num⟩
  | 16 => ⟨((225420879/36028797018963968), (-952447023/36028797018963968)), (173/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-425637625/2475880078570760549798248448)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778456127182693/633825300114114700748351602688), (-515637690391/158456325028528675187087900672)), (23101/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944695058500709/19807040628566084398385987584), (-2319908055703/39614081257132168796771975168)), (103967/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944571596125009/1237940039285380274899124224), (-2464329873827/2475880078570760549798248448)), (6905/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((55337794538379/4835703278458516698824704), (-2463686109727/154742504910672534362390528)), (110497/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549195974586381/9671406556917033397649408), (-2309021939401/9671406556917033397649408)), (103609/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258475896726255/604462909807314587353088), (-252463830719/75557863725914323419136)), (22669/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887283733662097/75557863725914323419136), (-820187161193/18889465931478580854784)), (73691/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297158191047413/4722366482869645213696), (-2459440977101/4722366482869645213696)), (110567/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620923832001293/590295810358705651712), (-3379911464651/590295810358705651712)), (152077/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113926199637929/4611686018427387904), (-4222161163977/73786976294838206464)), (190169/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821919430824233/9223372036854775808), (-2373091381069/4611686018427387904)), (214039/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398291948568203/288230376151711744), (-4741501098347/1152921504606846976)), (53541/288230376151711744), by norm_num⟩
  | 5 => ⟨((596932397832723/72057594037927936), (-4143552112899/144115188075855872)), (93767/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490563136813693/36028797018963968), (-6204819268827/36028797018963968)), (140791/18014398509481984), by norm_num⟩
  | 3 => ⟨((743957154961103/4503599627370496), (-967208064285/1125899906842624)), (176235/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112629878746099/2251799813685248), (-7710187074131/2251799813685248)), (353211/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212067424703867/2251799813685248), (-22993606627297/2251799813685248)), (1063347/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086322925852849/1125899906842624), (-11360495995667/562949953421312)), (2141619/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086322925852849/1125899906842624), (-11360495995667/562949953421312)), (8169628151900481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523839307822815/562949953421312), (-43844633698429/1125899906842624)), (2109557/1125899906842624), by norm_num⟩
  | 2 => ⟨((1946368630315821/2251799813685248), (-163194205301877/2251799813685248)), (2045147/562949953421312), by norm_num⟩
  | 3 => ⟨((1670538594759463/2251799813685248), (-141058756608145/1125899906842624)), (15327709/2251799813685248), by norm_num⟩
  | 4 => ⟨((1203974211579951/2251799813685248), (-418588003446075/2251799813685248)), (26582955/2251799813685248), by norm_num⟩
  | 5 => ⟨((565919749071761/2251799813685248), (-447614533372777/2251799813685248)), (38309355/2251799813685248), by norm_num⟩
  | 6 => ⟨((425993078689103/18014398509481984), (-1799903546435611/18014398509481984)), (68972109/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1731538869/33554432)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1776806487/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-195767851947243/2251799813685248), (-191124574361361/4503599627370496)), (78181635/4503599627370496), by norm_num⟩
  | 1 => ⟨((31599353/134217728), (493597929/4294967296)), (51/1073741824), by norm_num⟩
  | 2 => ⟨((-342290537/1073741824), (-668343985/4294967296)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((1235919943/4294967296), (603303021/4294967296)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-6536979/33554432), (-408443717/4294967296)), (87/2147483648), by norm_num⟩
  | 5 => ⟨((906366325/8589934592), (110608609/2147483648)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((-204540459/4294967296), (-399378221/17179869184)), (173/17179869184), by norm_num⟩
  | 7 => ⟨((1266070471/68719476736), (618020727/68719476736)), (135/34359738368), by norm_num⟩
  | 8 => ⟨((-428572799/68719476736), (-104601947/34359738368)), (185/137438953472), by norm_num⟩
  | 9 => ⟨((1031641471/549755813888), (503586353/549755813888)), (225/549755813888), by norm_num⟩
  | 10 => ⟨((-1117494757/2199023255552), (-272747425/1099511627776)), (123/1099511627776), by norm_num⟩
  | 11 => ⟨((275111991/2199023255552), (268586807/4398046511104)), (61/2199023255552), by norm_num⟩
  | 12 => ⟨((-496678055/17592186044416), (-60612213/4398046511104)), (111/17592186044416), by norm_num⟩
  | 13 => ⟨((827710219/140737488355328), (404039177/140737488355328)), (187/140737488355328), by norm_num⟩
  | 14 => ⟨((-640423093/562949953421312), (-625233357/1125899906842624)), (73/281474976710656), by norm_num⟩
  | 15 => ⟨((115619859/562949953421312), (225755109/2251799813685248)), (213/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1252417529/36028797018963968), (-76419521/4503599627370496)), (291/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-3500739226911/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889178759917929/316912650057057350374175801344), (-4141157806261/633825300114114700748351602688)), (1447/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889278820239997/39614081257132168796771975168), (-2328917466397/19807040628566084398385987584)), (52105/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889024458231991/2475880078570760549798248448), (-2473884105247/1237940039285380274899124224)), (55377/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885345075179949/77371252455336267181195264), (-4946439316613/154742504910672534362390528)), (27697/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193635447521455/1208925819614629174706176), (-4635875194553/9671406556917033397649408)), (25975/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258376977868505/604462909807314587353088), (-253436215659/37778931862957161709568)), (90949/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117945119735505/4722366482869645213696), (-3293348008099/37778931862957161709568)), (36965/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297035888241313/4722366482869645213696), (-77151684385/73786976294838206464)), (110955/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405188535263515/147573952589676412928), (-6785588908657/590295810358705651712)), (152659/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455651199246061/18446744073709551616), (-4238174697341/36893488147419103232)), (190969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821675099513507/9223372036854775808), (-2382036545731/2305843009213693952)), (105/4503599627370496), by norm_num⟩
  | 6 => ⟨((99557472065931/72057594037927936), (-9518468027555/1152921504606846976)), (215291/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193643197128635/144115188075855872), (-8317779100669/144115188075855872)), (94331/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490221991960965/36028797018963968), (-12454926570949/36028797018963968)), (70889/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487472634172645/9007199254740992), (-7765325917879/4503599627370496)), (177717/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112165460985921/2251799813685248), (-15473726884557/2251799813685248)), (44615/281474976710656), by norm_num⟩
  | 1 => ⟨((1105280666959543/1125899906842624), (-5767143627839/281474976710656)), (269553/562949953421312), by norm_num⟩
  | 0 => ⟨((1084593767494737/1125899906842624), (-2848179272613/70368744177664)), (1093171/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084593767494737/1125899906842624), (-2848179272613/70368744177664)), (4170116428855514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521479275958993/562949953421312), (-87797999634169/1125899906842624)), (2194625/1125899906842624), by norm_num⟩
  | 2 => ⟨((29977521916999/35184372088832), (-162660417685865/1125899906842624)), (551023/140737488355328), by norm_num⟩
  | 3 => ⟨((1587638558378819/2251799813685248), (-69294347841353/281474976710656)), (8785369/1125899906842624), by norm_num⟩
  | 4 => ⟨((491448430154281/1125899906842624), (-781699174799017/2251799813685248)), (33427843/2251799813685248), by norm_num⟩
  | 5 => ⟨((315332327470021/4503599627370496), (-341206913663571/1125899906842624)), (52390661/2251799813685248), by norm_num⟩
  | 6 => ⟨((-195767851947243/2251799813685248), (-191124574361361/4503599627370496)), (78181635/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1776806487/33554432)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile011Terms1

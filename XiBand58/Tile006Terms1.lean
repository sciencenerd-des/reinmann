/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile006Terms1
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
  | 0 => ⟨((15/16), (559/32)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (559/32))
  have he : value ((15/16), (559/32))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-69118709/33554432), (-321977985/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((111262806232515/1125899906842624), (-725188227156525/9007199254740992)), (61314941/4503599627370496), by norm_num⟩
  | 1 => ⟨((-932576647/4294967296), (379896497/2147483648)), (131/4294967296), by norm_num⟩
  | 2 => ⟨((1024540165/4294967296), (-26084935/134217728)), (73/2147483648), by norm_num⟩
  | 3 => ⟨((-750381611/4294967296), (611354243/4294967296)), (109/4294967296), by norm_num⟩
  | 4 => ⟨((824378459/8589934592), (-167910321/2147483648)), (61/4294967296), by norm_num⟩
  | 5 => ⟨((-724537845/17179869184), (590298695/17179869184)), (55/8589934592), by norm_num⟩
  | 6 => ⟨((1061314907/68719476736), (-864679201/68719476736)), (41/17179869184), by norm_num⟩
  | 7 => ⟨((-166567657/34359738368), (542826969/137438953472)), (105/137438953472), by norm_num⟩
  | 8 => ⟨((182993275/137438953472), (-596356379/549755813888)), (117/549755813888), by norm_num⟩
  | 9 => ⟨((-714804127/2199023255552), (582368397/2199023255552)), (29/549755813888), by norm_num⟩
  | 10 => ⟨((314117039/4398046511104), (-255918831/4398046511104)), (13/1099511627776), by norm_num⟩
  | 11 => ⟨((-1003906441/70368744177664), (817907121/70368744177664)), (169/70368744177664), by norm_num⟩
  | 12 => ⟨((367634651/140737488355328), (-149760469/70368744177664)), (63/140737488355328), by norm_num⟩
  | 13 => ⟨((-62136607/140737488355328), (809987405/2251799813685248)), (173/2251799813685248), by norm_num⟩
  | 14 => ⟨((312064183/4503599627370496), (-254246319/4503599627370496)), (55/4503599627370496), by norm_num⟩
  | 15 => ⟨((-365693383/36028797018963968), (297939339/36028797018963968)), (131/72057594037927936), by norm_num⟩
  | 16 => ⟨((803510489/576460752303423488), (-327319819/288230376151711744)), (73/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-890536967671/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778791185067639/633825300114114700748351602688), (-1053929806605/633825300114114700748351602688)), (5769/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((236220885000189/4951760157141521099596496896), (-1185457518805/39614081257132168796771975168)), (103849/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472385937737439/618970019642690137449562112), (-629641987795/1237940039285380274899124224)), (110347/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442802505945371/38685626227668133590597632), (-157373295411/19342813113834066795298816)), (27589/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549571578003133/9671406556917033397649408), (-1179983598475/9671406556917033397649408)), (25867/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258804591908395/604462909807314587353088), (-516084819767/302231454903657293676544)), (5659/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887817942273055/75557863725914323419136), (-1676683376481/75557863725914323419136)), (147151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297558916407341/4722366482869645213696), (-1256994509829/4722366482869645213696)), (55189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621474941016591/590295810358705651712), (-1727526094049/590295810358705651712)), (75897/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455877061846231/18446744073709551616), (-539536583393/18446744073709551616)), (47445/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822694844241901/9223372036854775808), (-606545395027/2305843009213693952)), (106777/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593943492071841/1152921504606846976), (-2424017102751/1152921504606846976)), (213617/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194543849303281/144115188075855872), (-529645610155/36028797018963968)), (186987/144115188075855872), by norm_num⟩
  | 4 => ⟨((372895587186143/9007199254740992), (-1586507443709/18014398509481984)), (280625/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489189419473541/9007199254740992), (-3957779855879/9007199254740992)), (351033/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113906609439443/2251799813685248), (-986268719939/562949953421312)), (351413/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107952788707337/1125899906842624), (-11771896418243/2251799813685248)), (528073/1125899906842624), by norm_num⟩
  | 0 => ⟨((272544141767827/281474976710656), (-2911457071377/281474976710656)), (1059981/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((272544141767827/281474976710656), (-2911457071377/281474976710656)), (4043506626609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2110932445864447/2251799813685248), (-5638160649911/281474976710656)), (4149253/2251799813685248), by norm_num⟩
  | 2 => ⟨((1977973919875685/2251799813685248), (-84567206577143/2251799813685248)), (7945597/2251799813685248), by norm_num⟩
  | 3 => ⟨((1734270156497129/2251799813685248), (-148567140000403/2251799813685248)), (1819447/281474976710656), by norm_num⟩
  | 4 => ⟨((331470493345329/562949953421312), (-228844105566521/2251799813685248)), (24341225/2251799813685248), by norm_num⟩
  | 5 => ⟨((1514871235284147/4503599627370496), (-134745669859813/1125899906842624)), (33612169/2251799813685248), by norm_num⟩
  | 6 => ⟨((111262806232515/1125899906842624), (-725188227156525/9007199254740992)), (61314941/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-321977985/8388608)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-9054133/4194304), (-674834713/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-424049655820697/4503599627370496), (-301084985224679/4503599627370496)), (94411921/4503599627370496), by norm_num⟩
  | 1 => ⟨((14549649/67108864), (82644677/536870912)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((-1072057757/4294967296), (-761185605/4294967296)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((822834737/4294967296), (292115771/2147483648)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((-236830875/2147483648), (-168155355/2147483648)), (221/8589934592), by norm_num⟩
  | 5 => ⟨((218129297/4294967296), (309753611/8589934592)), (205/17179869184), by norm_num⟩
  | 6 => ⟨((-334840845/17179869184), (-475489365/34359738368)), (159/34359738368), by norm_num⟩
  | 7 => ⟨((440571165/68719476736), (625631271/137438953472)), (53/34359738368), by norm_num⟩
  | 8 => ⟨((-1014452597/549755813888), (-720284619/549755813888)), (123/274877906944), by norm_num⟩
  | 9 => ⟨((1038161523/2199023255552), (737118501/2199023255552)), (127/1099511627776), by norm_num⟩
  | 10 => ⟨((-956182099/8796093022208), (-678911229/8796093022208)), (59/2199023255552), by norm_num⟩
  | 11 => ⟨((800614781/35184372088832), (35528429/2199023255552)), (199/35184372088832), by norm_num⟩
  | 12 => ⟨((-1228989107/281474976710656), (-27269077/8796093022208)), (77/70368744177664), by norm_num⟩
  | 13 => ⟨((217680923/281474976710656), (618233799/1125899906842624)), (55/281474976710656), by norm_num⟩
  | 14 => ⟨((-1145665939/9007199254740992), (-813449103/9007199254740992)), (73/2251799813685248), by norm_num⟩
  | 15 => ⟨((703464883/36028797018963968), (31217263/2251799813685248)), (91/18014398509481984), by norm_num⟩
  | 16 => ⟨((-809893877/288230376151711744), (-143760809/72057594037927936)), (53/72057594037927936), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (-3288015213589/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778631413712281/633825300114114700748351602688), (-3890655270451/633825300114114700748351602688)), (92583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118099184186557/2475880078570760549798248448), (-273509038215/2475880078570760549798248448)), (104181/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889351847150465/2475880078570760549798248448), (-2324313898829/1237940039285380274899124224)), (865/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1771017543953133/154742504910672534362390528), (-2323736928837/77371252455336267181195264)), (110753/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24209226821197/151115727451828646838272), (-4355780903087/9671406556917033397649408)), (103865/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258645552011559/604462909807314587353088), (-1905041350975/302231454903657293676544)), (22729/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235944794697687/9444732965739290427392), (-6189086944599/75557863725914323419136)), (147801/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297363227147959/4722366482869645213696), (-579975684401/590295810358705651712)), (27727/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810602121987921/295147905179352825856), (-99632307967/9223372036854775808)), (152589/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911583721466683/36893488147419103232), (-3982844578395/36893488147419103232)), (23859/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911154049515433/4611686018427387904), (-8954671856179/9223372036854775808)), (214919/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796776289833791/576460752303423488), (-8946265562891/1152921504606846976)), (107577/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194197123927393/144115188075855872), (-977316394167/18014398509481984)), (47131/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491052934272787/36028797018963968), (-11708908977425/36028797018963968)), (283315/36028797018963968), by norm_num⟩
  | 3 => ⟨((93031962015255/562949953421312), (-14603115706591/9007199254740992)), (1387/35184372088832), by norm_num⟩
  | 2 => ⟨((1113204317379849/2251799813685248), (-14553651115125/2251799813685248)), (356467/2251799813685248), by norm_num⟩
  | 1 => ⟨((276709780227927/281474976710656), (-10853523587819/562949953421312)), (134549/281474976710656), by norm_num⟩
  | 0 => ⟨((543855448604297/562949953421312), (-21460885501791/562949953421312)), (1090421/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((543855448604297/562949953421312), (-21460885501791/562949953421312)), (4159626011375045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049180935446473/1125899906842624), (-82931844588231/1125899906842624)), (1095005/562949953421312), by norm_num⟩
  | 2 => ⟨((971580988513603/1125899906842624), (-154561715041591/1125899906842624)), (4404191/1125899906842624), by norm_num⟩
  | 3 => ⟨((408597730532133/562949953421312), (-266754127918153/1125899906842624)), (4405141/562949953421312), by norm_num⟩
  | 4 => ⟨((1059864474979591/2251799813685248), (-193614246906001/562949953421312)), (33928067/2251799813685248), by norm_num⟩
  | 5 => ⟨((464987230625373/4503599627370496), (-182258530175259/562949953421312)), (110551537/4503599627370496), by norm_num⟩
  | 6 => ⟨((-424049655820697/4503599627370496), (-301084985224679/4503599627370496)), (94411921/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-674834713/16777216)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-75431263/33554432), (-1405535867/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-118835191393619/2251799813685248), (823944046141081/9007199254740992)), (10670315/562949953421312), by norm_num⟩
  | 1 => ⟨((271753639/2147483648), (-471051105/2147483648)), (197/4294967296), by norm_num⟩
  | 2 => ⟨((-325818383/2147483648), (564765609/2147483648)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((32553265/268435456), (-902832523/4294967296)), (3/67108864), by norm_num⟩
  | 4 => ⟨((-312237281/4294967296), (135306115/1073741824)), (233/8589934592), by norm_num⟩
  | 5 => ⟨((37435615/1073741824), (-1038239659/17179869184)), (113/8589934592), by norm_num⟩
  | 6 => ⟨((-478755649/34359738368), (829863323/34359738368)), (183/34359738368), by norm_num⟩
  | 7 => ⟨((41000211/8589934592), (-568550097/68719476736)), (253/137438953472), by norm_num⟩
  | 8 => ⟨((-393256849/274877906944), (681661795/274877906944)), (153/274877906944), by norm_num⟩
  | 9 => ⟨((209553053/549755813888), (-726468265/1099511627776)), (165/1099511627776), by norm_num⟩
  | 10 => ⟨((-100497255/1099511627776), (696797927/4398046511104)), (5/137438953472), by norm_num⟩
  | 11 => ⟨((701038233/35184372088832), (-1215162513/35184372088832)), (281/35184372088832), by norm_num⟩
  | 12 => ⟨((-560338755/140737488355328), (485638741/70368744177664)), (113/70368744177664), by norm_num⟩
  | 13 => ⟨((413425739/562949953421312), (-89577757/70368744177664)), (21/70368744177664), by norm_num⟩
  | 14 => ⟨((-566486643/4503599627370496), (119865/549755813888)), (29/562949953421312), by norm_num⟩
  | 15 => ⟨((362233505/18014398509481984), (-1255773381/36028797018963968)), (299/36028797018963968), by norm_num⟩
  | 16 => ⟨((-434299005/144115188075855872), (11762551/2251799813685248)), (91/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (1363876156275/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778496225120941/633825300114114700748351602688), (3227229190779/633825300114114700748351602688)), (46259/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889435032912403/39614081257132168796771975168), (907478082263/9903520314283042199192993792)), (104103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889190661174721/2475880078570760549798248448), (3855896444093/2475880078570760549798248448)), (55317/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885428304193529/77371252455336267181195264), (1927450298005/77371252455336267181195264)), (27665/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387309976343675/2417851639229258349412352), (1806455740013/4835703278458516698824704)), (25943/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258514032971195/604462909807314587353088), (3160240008425/604462909807314587353088)), (90829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471836284263691/18889465931478580854784), (641675969163/9444732965739290427392)), (147649/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81075234191993/295147905179352825856), (3848321957811/4722366482869645213696)), (1731/73786976294838206464), by norm_num⟩
  | 9 => ⟨((810492832799013/295147905179352825856), (5288626337721/590295810358705651712)), (152403/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822895278885359/73786976294838206464), (1651640106707/18446744073709551616)), (190617/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911001684302083/4611686018427387904), (7426577857241/9223372036854775808)), (214599/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593249664061541/1152921504606846976), (3709664769941/576460752303423488)), (107397/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193934110545449/144115188075855872), (3241882905371/72057594037927936)), (188165/144115188075855872), by norm_num⟩
  | 4 => ⟨((372665620001461/9007199254740992), (9709370689421/36028797018963968)), (282687/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488030417679113/9007199254740992), (6054132578999/4503599627370496)), (22133/562949953421312), by norm_num⟩
  | 2 => ⟨((1112733938996713/2251799813685248), (24131339016275/4503599627370496)), (710571/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212319782095585/2251799813685248), (17992283296535/1125899906842624)), (1071657/2251799813685248), by norm_num⟩
  | 0 => ⟨((135807109263725/140737488355328), (71122581166359/2251799813685248)), (541651/562949953421312), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((135807109263725/140737488355328), (71122581166359/2251799813685248)), (2066234590770530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((261818108063249/281474976710656), (137261965727161/2251799813685248)), (4318269/2251799813685248), by norm_num⟩
  | 2 => ⟨((1939904833300483/2251799813685248), (255352490624203/2251799813685248)), (4279929/1125899906842624), by norm_num⟩
  | 3 => ⟨((205281673204249/281474976710656), (109991911302833/562949953421312)), (8344921/1125899906842624), by norm_num⟩
  | 4 => ⟨((277935969105581/562949953421312), (641742974243553/2251799813685248)), (7716481/562949953421312), by norm_num⟩
  | 5 => ⟨((731983719656503/4503599627370496), (1267348576043615/4503599627370496)), (24035437/1125899906842624), by norm_num⟩
  | 6 => ⟨((-118835191393619/2251799813685248), (823944046141081/9007199254740992)), (10670315/562949953421312), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-1405535867/33554432)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-19542101/8388608), (-364134483/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((92020876575963/1125899906842624), (59514112257003/1125899906842624)), (87464291/9007199254740992), by norm_num⟩
  | 1 => ⟨((-218070305/1073741824), (-564144185/4294967296)), (53/2147483648), by norm_num⟩
  | 2 => ⟨((541884351/2147483648), (350461409/2147483648)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((-448844009/2147483648), (-145143981/1073741824)), (113/4294967296), by norm_num⟩
  | 4 => ⟨((557667731/4294967296), (721338487/8589934592)), (143/8589934592), by norm_num⟩
  | 5 => ⟨((-554300901/8589934592), (-716983521/17179869184)), (9/1073741824), by norm_num⟩
  | 6 => ⟨((459128665/17179869184), (72495/4194304)), (61/17179869184), by norm_num⟩
  | 7 => ⟨((-651938213/68719476736), (-843276557/137438953472)), (11/8589934592), by norm_num⟩
  | 8 => ⟨((50625175/17179869184), (523865881/274877906944)), (111/274877906944), by norm_num⟩
  | 9 => ⟨((-447284743/549755813888), (-578559027/1099511627776)), (31/274877906944), by norm_num⟩
  | 10 => ⟨((444584333/2199023255552), (575066069/4398046511104)), (63/2199023255552), by norm_num⟩
  | 11 => ⟨((-803454957/17592186044416), (-259815545/8796093022208)), (29/4398046511104), by norm_num⟩
  | 12 => ⟨((332751761/35184372088832), (6725181/1099511627776)), (49/35184372088832), by norm_num⟩
  | 13 => ⟨((-127208779/70368744177664), (-82271739/70368744177664)), (19/70368744177664), by norm_num⟩
  | 14 => ⟨((361259361/1125899906842624), (467285923/2251799813685248)), (55/1125899906842624), by norm_num⟩
  | 15 => ⟨((-478771087/9007199254740992), (-619286345/18014398509481984)), (37/4503599627370496), by norm_num⟩
  | 16 => ⟨((594850729/72057594037927936), (384717189/72057594037927936)), (187/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (747808677305/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889187838774807/316912650057057350374175801344), (884620274853/633825300114114700748351602688)), (721/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((472324933387165/9903520314283042199192993792), (497498263605/19807040628566084398385987584)), (103829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889047319443671/2475880078570760549798248448), (1056932667609/2475880078570760549798248448)), (55163/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770713731830171/154742504910672534362390528), (1056650252215/154742504910672534362390528)), (110333/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774553226262195/4835703278458516698824704), (247577412447/2417851639229258349412352)), (103445/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258397755282349/604462909807314587353088), (866221099717/604462909807314587353088)), (45261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943578555223885/37778931862957161709568), (175880916259/9444732965739290427392)), (18389/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297063535396285/4722366482869645213696), (527397017661/2361183241434822606848)), (110347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810397093270343/295147905179352825856), (1449543641137/590295810358705651712)), (37937/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911328947754793/36893488147419103232), (1810733134947/73786976294838206464)), (47429/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821739010656393/9223372036854775808), (254428879389/1152921504606846976)), (213473/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592988672851027/1152921504606846976), (1016689176311/576460752303423488)), (213527/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193709522301769/144115188075855872), (888449765237/72057594037927936)), (186897/144115188075855872), by norm_num⟩
  | 4 => ⟨((186291641815093/4503599627370496), (2660743080221/36028797018963968)), (280467/36028797018963968), by norm_num⟩
  | 3 => ⟨((92976992352707/562949953421312), (1620060225/4398046511104)), (87699/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224710032970939/4503599627370496), (3305845752353/2251799813685248)), (175559/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211280437843157/2251799813685248), (9857563510761/2251799813685248)), (1054971/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085610391788697/1125899906842624), (19476512946581/2251799813685248)), (2116461/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1085610391788697/1125899906842624), (19476512946581/2251799813685248)), (8073657998091887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((261669594685647/281474976710656), (37559119993019/2251799813685248)), (4118063/2251799813685248), by norm_num⟩
  | 2 => ⟨((972717867723061/1125899906842624), (17458176602721/562949953421312)), (7793985/2251799813685248), by norm_num⟩
  | 3 => ⟨((419646938739207/562949953421312), (120663517004483/2251799813685248)), (13950595/2251799813685248), by norm_num⟩
  | 4 => ⟨((1244825205917227/2251799813685248), (179895478170655/2251799813685248)), (22293835/2251799813685248), by norm_num⟩
  | 5 => ⟨((673784321767731/2251799813685248), (198897277010491/2251799813685248)), (28210757/2251799813685248), by norm_num⟩
  | 6 => ⟨((92020876575963/1125899906842624), (59514112257003/1125899906842624)), (87464291/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-364134483/8388608)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-40343165/16777216), (-1503455285/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((34524537665731/562949953421312), (-298484259920159/4503599627370496)), (47563241/4503599627370496), by norm_num⟩
  | 1 => ⟨((-168902761/1073741824), (365065103/2147483648)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((866454057/4294967296), (-468186751/2147483648)), (77/2147483648), by norm_num⟩
  | 3 => ⟨((-92600449/536870912), (400291769/2147483648)), (67/2147483648), by norm_num⟩
  | 4 => ⟨((950061849/8589934592), (-256682029/2147483648)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-243686053/4294967296), (1053402249/17179869184)), (181/17179869184), by norm_num⟩
  | 6 => ⟨((833389847/34359738368), (-900641141/34359738368)), (157/34359738368), by norm_num⟩
  | 7 => ⟨((-152685911/17179869184), (330014131/34359738368)), (117/68719476736), by norm_num⟩
  | 8 => ⟨((783263259/274877906944), (-846469533/274877906944)), (19/34359738368), by norm_num⟩
  | 9 => ⟨((-446451243/549755813888), (120619527/137438953472)), (11/68719476736), by norm_num⟩
  | 10 => ⟨((916099863/4398046511104), (-990025531/4398046511104)), (183/4398046511104), by norm_num⟩
  | 11 => ⟨((-106806807/2199023255552), (461702791/8796093022208)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((91318017/8796093022208), (-789496185/70368744177664)), (75/35184372088832), by norm_num⟩
  | 13 => ⟨((-576556527/281474976710656), (623082379/281474976710656)), (15/35184372088832), by norm_num⟩
  | 14 => ⟨((422525227/1125899906842624), (-913242713/2251799813685248)), (89/1125899906842624), by norm_num⟩
  | 15 => ⟨((-289001549/4503599627370496), (624645683/9007199254740992)), (31/2251799813685248), by norm_num⟩
  | 16 => ⟨((370637169/36028797018963968), (-50068267/4503599627370496)), (161/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (-268390739117/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222282451108409/79228162514264337593543950336), (-1269813955243/633825300114114700748351602688)), (46163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889169158383883/39614081257132168796771975168), (-714121317997/19807040628566084398385987584)), (103875/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888908584055621/2475880078570760549798248448), (-1517135669709/2475880078570760549798248448)), (13797/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770574997279879/154742504910672534362390528), (-379179300437/38685626227668133590597632)), (55193/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96811024361795/604462909807314587353088), (-1421477911493/9671406556917033397649408)), (51749/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314570987827723/151115727451828646838272), (-1243348884157/604462909807314587353088)), (90573/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943486090379763/37778931862957161709568), (-1009804635711/37778931862957161709568)), (147201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296924839710909/4722366482869645213696), (-1513978746625/4722366482869645213696)), (110419/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810301741304861/295147905179352825856), (-130033633967/36893488147419103232)), (151855/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822419519668677/73786976294838206464), (-2598899959325/73786976294838206464)), (23733/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821470843627153/9223372036854775808), (-2921326960955/9223372036854775808)), (106829/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592720513348495/1152921504606846976), (-1459142793401/576460752303423488)), (26717/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193474891598303/144115188075855872), (-2550082452855/144115188075855872)), (93553/72057594037927936), by norm_num⟩
  | 4 => ⟨((744990603584807/18014398509481984), (-3818299071025/36028797018963968)), (1097/140737488355328), by norm_num⟩
  | 3 => ⟨((1487192003387697/9007199254740992), (-4760953830553/9007199254740992)), (175673/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111915199013793/2251799813685248), (-9486239684675/4503599627370496)), (87951/562949953421312), by norm_num⟩
  | 1 => ⟨((276245162483881/281474976710656), (-7070255480695/1125899906842624)), (528859/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084291973615675/1125899906842624), (-13963774790017/1125899906842624)), (2124719/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1084291973615675/1125899906842624), (-13963774790017/1125899906842624)), (8105159768111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088096978953383/2251799813685248), (-13447739745047/562949953421312)), (4145103/2251799813685248), by norm_num⟩
  | 2 => ⟨((967505081882755/1125899906842624), (-24940214103161/562949953421312)), (1971389/562949953421312), by norm_num⟩
  | 3 => ⟨((1658367712222227/2251799813685248), (-85726213285583/1125899906842624)), (14251091/2251799813685248), by norm_num⟩
  | 4 => ⟨((302068096576407/562949953421312), (-252536807827907/2251799813685248)), (23160971/2251799813685248), by norm_num⟩
  | 5 => ⟨((310006980131125/1125899906842624), (-542025538095869/4503599627370496)), (60100831/4503599627370496), by norm_num⟩
  | 6 => ⟨((34524537665731/562949953421312), (-298484259920159/4503599627370496)), (47563241/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-1503455285/33554432)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-83017565/33554432), (-1546893967/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-790502940273043/18014398509481984), (-1295325954131579/18014398509481984)), (137024437/9007199254740992), by norm_num⟩
  | 1 => ⟨((248692343/2147483648), (815019477/4294967296)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((-328156675/2147483648), (-537720781/2147483648)), (29/536870912), by norm_num⟩
  | 3 => ⟨((577349519/4294967296), (946050645/4294967296)), (103/2147483648), by norm_num⟩
  | 4 => ⟨((-95228655/1073741824), (-78021309/536870912)), (137/4294967296), by norm_num⟩
  | 5 => ⟨((6282847/134217728), (1317777327/17179869184)), (73/4294967296), by norm_num⟩
  | 6 => ⟨((-353723593/17179869184), (-1159229971/34359738368)), (259/34359738368), by norm_num⟩
  | 7 => ⟨((266713383/34359738368), (437039193/34359738368)), (197/68719476736), by norm_num⟩
  | 8 => ⟨((-175967977/68719476736), (-1153371485/274877906944)), (131/137438953472), by norm_num⟩
  | 9 => ⟨((412790737/549755813888), (676402993/549755813888)), (39/137438953472), by norm_num⟩
  | 10 => ⟨((-54468921/274877906944), (-357013255/1099511627776)), (83/1099511627776), by norm_num⟩
  | 11 => ⟨((209085971/4398046511104), (685220689/8796093022208)), (161/8796093022208), by norm_num⟩
  | 12 => ⟨((-735719819/70368744177664), (-1205557787/70368744177664)), (143/35184372088832), by norm_num⟩
  | 13 => ⟨((597417471/281474976710656), (978934189/281474976710656)), (117/140737488355328), by norm_num⟩
  | 14 => ⟨((-450462559/1125899906842624), (-738132413/1125899906842624)), (89/562949953421312), by norm_num⟩
  | 15 => ⟨((634024809/9007199254740992), (129864917/1125899906842624)), (253/9007199254740992), by norm_num⟩
  | 16 => ⟨((-418306955/36028797018963968), (-342720961/18014398509481984)), (169/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (-2759889616953/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889073862148157/316912650057057350374175801344), (-3264032420697/633825300114114700748351602688)), (46261/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236130380756935/4951760157141521099596496896), (-917809865203/9903520314283042199192993792)), (26027/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888774266094453/2475880078570760549798248448), (-3899706632119/2475880078570760549798248448)), (110639/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770440315652837/154742504910672534362390528), (-3898598499309/154742504910672534362390528)), (110665/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548849739677951/9671406556917033397649408), (-3653759039953/9671406556917033397649408)), (103777/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629086373363495/302231454903657293676544), (-3195862486793/604462909807314587353088)), (45417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886790750793787/75557863725914323419136), (-2595535543085/37778931862957161709568)), (73829/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296788135773703/4722366482869645213696), (-1945687174385/2361183241434822606848)), (110791/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810207244977011/295147905179352825856), (-2673753336551/295147905179352825856)), (76207/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822181744157693/73786976294838206464), (-834960800481/9223372036854775808)), (23829/9223372036854775808), by norm_num⟩
  | 7 => ⟨((56912538747111/288230376151711744), (-469262075971/576460752303423488)), (214619/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592448282680335/1152921504606846976), (-937516522213/144115188075855872)), (6713/36028797018963968), by norm_num⟩
  | 5 => ⟨((596616871265453/72057594037927936), (-3276777925197/72057594037927936)), (94093/72057594037927936), by norm_num⟩
  | 4 => ⟨((186201701159567/4503599627370496), (-4906118155137/18014398509481984)), (70681/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486722271298101/9007199254740992), (-12233674618431/9007199254740992)), (177093/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222860410316753/4503599627370496), (-24372685952441/4503599627370496)), (710715/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104215319703041/1125899906842624), (-18161533299109/1125899906842624)), (66997/140737488355328), by norm_num⟩
  | 0 => ⟨((541305917977569/562949953421312), (-17926613379405/562949953421312)), (2167517/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((541305917977569/562949953421312), (-17926613379405/562949953421312)), (8268421181685637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519923186051379/562949953421312), (-137899034933295/2251799813685248)), (4306409/2251799813685248), by norm_num⟩
  | 2 => ⟨((956147553680239/1125899906842624), (-127359288619163/1125899906842624)), (4240989/1125899906842624), by norm_num⟩
  | 3 => ⟨((797582227828221/1125899906842624), (-216314561377239/1125899906842624)), (4081305/562949953421312), by norm_num⟩
  | 4 => ⟨((261721942200133/562949953421312), (-153236223510105/562949953421312)), (1837651/140737488355328), by norm_num⟩
  | 5 => ⟨((319865270863111/2251799813685248), (-1139860672551503/4503599627370496)), (86691705/4503599627370496), by norm_num⟩
  | 6 => ⟨((-790502940273043/18014398509481984), (-1295325954131579/18014398509481984)), (137024437/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-1546893967/33554432)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-85187893/33554432), (-793667207/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1398854015194551/18014398509481984), (257963983247403/18014398509481984)), (243467689/18014398509481984), by norm_num⟩
  | 1 => ⟨((903169369/4294967296), (-20819289/536870912)), (317/8589934592), by norm_num⟩
  | 2 => ⟨((-305728499/1073741824), (225518719/4294967296)), (217/4294967296), by norm_num⟩
  | 3 => ⟨((275976041/1073741824), (-50893001/1073741824)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((-747356973/4294967296), (275641603/8589934592)), (269/8589934592), by norm_num⟩
  | 5 => ⟨((1619104161/17179869184), (-298580519/17179869184)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((-1461538449/34359738368), (134761839/17179869184)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((282708535/17179869184), (-104269093/34359738368)), (209/68719476736), by norm_num⟩
  | 8 => ⟨((-765588905/137438953472), (141182969/137438953472)), (285/274877906944), by norm_num⟩
  | 9 => ⟨((921445861/549755813888), (-169924697/549755813888)), (173/549755813888), by norm_num⟩
  | 10 => ⟨((-249532165/549755813888), (46016461/549755813888)), (189/2199023255552), by norm_num⟩
  | 11 => ⟨((491451367/4398046511104), (-181258017/8796093022208)), (47/2199023255552), by norm_num⟩
  | 12 => ⟨((-443624991/17592186044416), (163618603/35184372088832)), (171/35184372088832), by norm_num⟩
  | 13 => ⟨((369648845/70368744177664), (-68167291/70368744177664)), (9/8796093022208), by norm_num⟩
  | 14 => ⟨((-143003947/140737488355328), (105485969/562949953421312)), (225/1125899906842624), by norm_num⟩
  | 15 => ⟨((1652317301/9007199254740992), (-152352693/4503599627370496)), (327/9007199254740992), by norm_num⟩
  | 16 => ⟨((-559319775/18014398509481984), (103144685/18014398509481984)), (7/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (481841018089/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444510663974925/158456325028528675187087900672), (1139593915791/158456325028528675187087900672)), (92649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888924570509557/39614081257132168796771975168), (2563508443565/19807040628566084398385987584)), (26065/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888648018343297/2475880078570760549798248448), (5446041770467/2475880078570760549798248448)), (110809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770313654923465/154742504910672534362390528), (340278225825/9671406556917033397649408)), (110847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24198914950347/151115727451828646838272), (5102484208865/9671406556917033397649408)), (103959/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39314625741231/18889465931478580854784), (4462984912457/604462909807314587353088)), (22751/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471654938879333/18889465931478580854784), (7249184906161/75557863725914323419136)), (36989/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162082396544099/590295810358705651712), (84908119815/73786976294838206464)), (111033/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202529500228439/73786976294838206464), (3733708264179/295147905179352825856)), (152777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821956891738467/73786976294838206464), (9327526488199/73786976294838206464)), (191131/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820945889991345/9223372036854775808), (2621049674355/2305843009213693952)), (215243/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398047487768137/288230376151711744), (10472619902081/1152921504606846976)), (107759/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193004357568969/144115188075855872), (4575262921187/72057594037927936)), (94445/72057594037927936), by norm_num⟩
  | 4 => ⟨((93078929136353/2251799813685248), (6849889786367/18014398509481984)), (70989/9007199254740992), by norm_num⟩
  | 3 => ⟨((371568057836065/2251799813685248), (2134907791739/1125899906842624)), (356035/9007199254740992), by norm_num⟩
  | 2 => ⟨((555481427968663/1125899906842624), (4252794295651/562949953421312)), (178837/1125899906842624), by norm_num⟩
  | 1 => ⟨((551735698668537/562949953421312), (12673465848091/562949953421312)), (270309/562949953421312), by norm_num⟩
  | 0 => ⟨((135119329482619/140737488355328), (50016804925783/1125899906842624)), (548869/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((135119329482619/140737488355328), (50016804925783/1125899906842624)), (2093769075633811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1035581615140213/1125899906842624), (24010081547611/281474976710656)), (1102683/562949953421312), by norm_num⟩
  | 2 => ⟨((1888632427980577/2251799813685248), (88336090544499/562949953421312)), (4433149/1125899906842624), by norm_num⟩
  | 3 => ⟨((1528590680582569/2251799813685248), (592714873318447/2251799813685248)), (8827621/1125899906842624), by norm_num⟩
  | 4 => ⟨((27551274424539/70368744177664), (804706018795237/2251799813685248)), (8316051/562949953421312), by norm_num⟩
  | 5 => ⟨((57615552803799/2251799813685248), (1260257042469323/4503599627370496)), (99644711/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1398854015194551/18014398509481984), (257963983247403/18014398509481984)), (243467689/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-793667207/16777216)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile006Terms1

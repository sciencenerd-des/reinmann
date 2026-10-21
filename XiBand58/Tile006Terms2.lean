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
namespace Reinmann.XiBand58.Tile006Terms2
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
  | 0 => ⟨((-21804525/8388608), (-812581963/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-172770456254645/9007199254740992), (323393155014765/4503599627370496)), (231852185/18014398509481984), by norm_num⟩
  | 1 => ⟨((57103803/1073741824), (-855098929/4294967296)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((-9895335/134217728), (148177353/536870912)), (217/4294967296), by norm_num⟩
  | 3 => ⟨((292647405/4294967296), (-1095559621/4294967296)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((-405695447/8589934592), (1518768125/8589934592)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((56241331/2147483648), (-842183875/8589934592)), (315/17179869184), by norm_num⟩
  | 6 => ⟨((-207912107/17179869184), (1556686343/34359738368)), (147/17179869184), by norm_num⟩
  | 7 => ⟨((164701361/34359738368), (-308289357/17179869184)), (235/68719476736), by norm_num⟩
  | 8 => ⟨((-28540571/17179869184), (427379797/68719476736)), (165/137438953472), by norm_num⟩
  | 9 => ⟨((140677805/274877906944), (-1053287471/549755813888)), (205/549755813888), by norm_num⟩
  | 10 => ⟨((-312033357/2199023255552), (1168133185/2199023255552)), (115/1099511627776), by norm_num⟩
  | 11 => ⟨((39324553/1099511627776), (-1177728325/8796093022208)), (117/4398046511104), by norm_num⟩
  | 12 => ⟨((-9085901/1099511627776), (1088452091/35184372088832)), (109/17592186044416), by norm_num⟩
  | 13 => ⟨((15502441/8796093022208), (-928563075/140737488355328)), (47/35184372088832), by norm_num⟩
  | 14 => ⟨((-98244327/281474976710656), (1471156291/1125899906842624)), (75/281474976710656), by norm_num⟩
  | 15 => ⟨((290550521/4503599627370496), (-1087709691/4503599627370496)), (7/140737488355328), by norm_num⟩
  | 16 => ⟨((-402788549/36028797018963968), (1507885811/36028797018963968)), (313/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (74567320145/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777956330414501/633825300114114700748351602688), (705361057323/158456325028528675187087900672)), (46239/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888827856661465/39614081257132168796771975168), (1586703062809/19807040628566084398385987584)), (13007/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236068224110931/309485009821345068724781056), (3370849659773/2475880078570760549798248448)), (27645/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770212028535597/154742504910672534362390528), (3369843891877/154742504910672534362390528)), (110603/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774317959058217/4835703278458516698824704), (1579080187727/4835703278458516698824704)), (25929/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314496462587107/151115727451828646838272), (1381161227431/302231454903657293676544)), (11347/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943243707103325/37778931862957161709568), (4486772574747/75557863725914323419136)), (147557/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648280478423237/2361183241434822606848), (840832260465/1180591620717411303424)), (27677/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620102644148065/590295810358705651712), (288858415013/36893488147419103232)), (76145/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821792723872067/73786976294838206464), (2886453446555/36893488147419103232)), (95231/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455191168195367/2305843009213693952), (405541583575/576460752303423488)), (107203/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398003266084665/288230376151711744), (3240676730955/576460752303423488)), (214577/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192854441001027/144115188075855872), (1415741930881/36028797018963968)), (187947/144115188075855872), by norm_num⟩
  | 4 => ⟨((93065479929407/2251799813685248), (4239020856633/18014398509481984)), (141153/18014398509481984), by norm_num⟩
  | 3 => ⟨((743010065267379/4503599627370496), (2642221774135/2251799813685248)), (353557/9007199254740992), by norm_num⟩
  | 2 => ⟨((277683985175281/562949953421312), (5262996923787/1125899906842624)), (88643/562949953421312), by norm_num⟩
  | 1 => ⟨((1103193501851607/1125899906842624), (31364244237943/2251799813685248)), (1068807/2251799813685248), by norm_num⟩
  | 0 => ⟨((540322923121629/562949953421312), (61877902579863/2251799813685248)), (2158069/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((540322923121629/562949953421312), (61877902579863/2251799813685248)), (8232379921920012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072721063754355/2251799813685248), (118781603925509/2251799813685248)), (2130631/1125899906842624), by norm_num⟩
  | 2 => ⟨((475404553357247/562949953421312), (109335266370771/1125899906842624)), (8294315/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584659082956191/2251799813685248), (369329338491241/2251799813685248)), (15619811/2251799813685248), by norm_num⟩
  | 4 => ⟨((263649130186081/562949953421312), (519816270776327/2251799813685248)), (423563/35184372088832), by norm_num⟩
  | 5 => ⟨((93476878038315/562949953421312), (973792478808029/4503599627370496)), (18953387/1125899906842624), by norm_num⟩
  | 6 => ⟨((-172770456254645/9007199254740992), (323393155014765/4503599627370496)), (231852185/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-812581963/16777216)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-1660699289/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((452832340851873/9007199254740992), (883104767230977/18014398509481984)), (72057229/9007199254740992), by norm_num⟩
  | 1 => ⟨((-305884035/2147483648), (-596529057/4294967296)), (99/4294967296), by norm_num⟩
  | 2 => ⟨((433317365/2147483648), (422523521/2147483648)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((-409226847/2147483648), (-798066185/4294967296)), (17/536870912), by norm_num⟩
  | 4 => ⟨((289856741/2147483648), (565272941/4294967296)), (49/2147483648), by norm_num⟩
  | 5 => ⟨((-656980789/8589934592), (-40038471/536870912)), (113/8589934592), by norm_num⟩
  | 6 => ⟨((620455579/17179869184), (302500081/8589934592)), (109/17179869184), by norm_num⟩
  | 7 => ⟨((-502252293/34359738368), (-489741295/34359738368)), (179/68719476736), by norm_num⟩
  | 8 => ⟨((711493949/137438953472), (346885393/68719476736)), (129/137438953472), by norm_num⟩
  | 9 => ⟨((-111989675/68719476736), (-27300009/17179869184)), (165/549755813888), by norm_num⟩
  | 10 => ⟨((1015330053/2199023255552), (990038397/2199023255552)), (189/2199023255552), by norm_num⟩
  | 11 => ⟨((-1046053329/8796093022208), (-1019996363/8796093022208)), (197/8796093022208), by norm_num⟩
  | 12 => ⟨((987897417/35184372088832), (481644551/17592186044416)), (47/8796093022208), by norm_num⟩
  | 13 => ⟨((-861207429/140737488355328), (-839754935/140737488355328)), (83/70368744177664), by norm_num⟩
  | 14 => ⟨((348569197/281474976710656), (679772825/562949953421312)), (17/70368744177664), by norm_num⟩
  | 15 => ⟨((-16459515/70368744177664), (-1027168767/4503599627370496)), (13/281474976710656), by norm_num⟩
  | 16 => ⟨((746133081/18014398509481984), (90943383/2251799813685248)), (75/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (251660291045/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777872303095597/633825300114114700748351602688), (595082080547/316912650057057350374175801344)), (46159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888733540923827/39614081257132168796771975168), (334657009459/9903520314283042199192993792)), (103865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888445867660539/2475880078570760549798248448), (710953553657/1237940039285380274899124224)), (110365/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110632026491919/9671406556917033397649408), (1421473991321/154742504910672534362390528)), (110375/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193567859885405/1208925819614629174706176), (1332171862645/9671406556917033397649408)), (103487/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257904781245189/604462909807314587353088), (582595289949/302231454903657293676544)), (45281/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943178156947369/37778931862957161709568), (946286500705/37778931862957161709568)), (147183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648231594178433/2361183241434822606848), (1418676205171/4722366482869645213696)), (27601/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809984558017159/295147905179352825856), (243682010331/73786976294838206464)), (75917/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821627167058539/73786976294838206464), (608746493779/18446744073709551616)), (94917/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820580278929901/9223372036854775808), (1368419801441/4611686018427387904)), (213621/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591830987553563/1152921504606846976), (2733693536229/1152921504606846976)), (106847/576460752303423488), by norm_num⟩
  | 5 => ⟨((596348861901863/72057594037927936), (2388447267313/144115188075855872)), (23383/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488817786311551/36028797018963968), (1787806800295/18014398509481984)), (35095/4503599627370496), by norm_num⟩
  | 3 => ⟨((742870898960553/4503599627370496), (2228596674471/4503599627370496)), (87809/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110471082781605/2251799813685248), (8877522007041/4503599627370496)), (351669/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205659280909835/2251799813685248), (3306123043075/562949953421312)), (1057183/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160100531908863/2251799813685248), (3260504756243/281474976710656)), (1061569/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2160100531908863/2251799813685248), (3260504756243/281474976710656)), (4049564365867232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2071833340849577/2251799813685248), (50043653191181/2251799813685248)), (4122545/2251799813685248), by norm_num⟩
  | 2 => ⟨((952568918195773/1125899906842624), (92088211882137/2251799813685248)), (7769371/2251799813685248), by norm_num⟩
  | 3 => ⟨((1608078087082193/2251799813685248), (77911338155401/1125899906842624)), (13782035/2251799813685248), by norm_num⟩
  | 4 => ⟨((284398552230643/562949953421312), (222555335268295/2251799813685248)), (337371/35184372088832), by norm_num⟩
  | 5 => ⟨((276354429766321/1125899906842624), (449733868929829/4503599627370496)), (26084025/2251799813685248), by norm_num⟩
  | 6 => ⟨((452832340851873/9007199254740992), (883104767230977/18014398509481984)), (72057229/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-1660699289/33554432)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-1694202921/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1168544009183637/18014398509481984), (-268310907308909/18014398509481984)), (91976269/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1610530187/8589934592), (46224491/1073741824)), (129/8589934592), by norm_num⟩
  | 2 => ⟨((581878871/2147483648), (-267211927/4294967296)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((-1121230837/4294967296), (257447269/4294967296)), (93/4294967296), by norm_num⟩
  | 4 => ⟨((1620386973/8589934592), (-186029579/4294967296)), (17/1073741824), by norm_num⟩
  | 5 => ⟨((-936704149/8589934592), (215077857/8589934592)), (5/536870912), by norm_num⟩
  | 6 => ⟨((451237203/8589934592), (-207218321/17179869184)), (79/17179869184), by norm_num⟩
  | 7 => ⟨((-1490563735/68719476736), (85562569/17179869184)), (33/17179869184), by norm_num⟩
  | 8 => ⟨((1077070831/137438953472), (-247307633/137438953472)), (97/137438953472), by norm_num⟩
  | 9 => ⟨((-1383615605/549755813888), (317693777/549755813888)), (127/549755813888), by norm_num⟩
  | 10 => ⟨((399916347/549755813888), (-2869541/17179869184)), (149/2199023255552), by norm_num⟩
  | 11 => ⟨((-1681319149/8796093022208), (193024937/4398046511104)), (159/8796093022208), by norm_num⟩
  | 12 => ⟨((202484891/4398046511104), (-371942551/35184372088832)), (155/35184372088832), by norm_num⟩
  | 13 => ⟨((-1440631657/140737488355328), (165392653/70368744177664)), (35/35184372088832), by norm_num⟩
  | 14 => ⟨((1189703159/562949953421312), (-34146161/70368744177664)), (59/281474976710656), by norm_num⟩
  | 15 => ⟨((-458491255/1125899906842624), (210549545/2251799813685248)), (93/2251799813685248), by norm_num⟩
  | 16 => ⟨((1325210175/18014398509481984), (-304283229/18014398509481984)), (17/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (-73499596775/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55555952316225/19807040628566084398385987584), (-173783559579/316912650057057350374175801344)), (92235/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888641542781573/39614081257132168796771975168), (-390921923053/39614081257132168796771975168)), (51883/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888348197533069/2475880078570760549798248448), (-207619905009/1237940039285380274899124224)), (55127/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442503710323803/38685626227668133590597632), (-415110803637/154742504910672534362390528)), (55129/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548451488380153/9671406556917033397649408), (-389029365731/9671406556917033397649408)), (51685/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257824907270991/604462909807314587353088), (-664577629/1180591620717411303424)), (22613/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943113346353867/37778931862957161709568), (-552671943329/75557863725914323419136)), (146989/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648183062292805/2361183241434822606848), (-414279529229/4722366482869645213696)), (110247/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619835900262285/590295810358705651712), (-569269910133/590295810358705651712)), (75799/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910730508612161/36893488147419103232), (-355520583445/36893488147419103232)), (94755/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910196934079181/4611686018427387904), (-99896372311/1152921504606846976)), (6663/288230376151711744), by norm_num⟩
  | 6 => ⟨((1591645210332441/1152921504606846976), (-798234138453/1152921504606846976)), (106619/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192535879846693/144115188075855872), (-697402406183/144115188075855872)), (11663/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488576438525449/36028797018963968), (-261000593471/9007199254740992)), (139981/18014398509481984), by norm_num⟩
  | 3 => ⟨((742721292903999/4503599627370496), (-1301334102589/9007199254740992)), (350041/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220351122743519/4503599627370496), (-2591694722029/4503599627370496)), (700347/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102395521567509/1125899906842624), (-3860223916131/2251799813685248)), (16425/35184372088832), by norm_num⟩
  | 0 => ⟨((2158436603957813/2251799813685248), (-3805932817029/1125899906842624)), (1052591/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2158436603957813/2251799813685248), (-3805932817029/1125899906842624)), (4015316013816451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034459325489957/1125899906842624), (-7296265551275/1125899906842624)), (4050029/2251799813685248), by norm_num⟩
  | 2 => ⟨((950397858725209/1125899906842624), (-13407390647955/1125899906842624)), (1873675/562949953421312), by norm_num⟩
  | 3 => ⟨((1604185818396565/2251799813685248), (-45269940197943/2251799813685248)), (400981/70368744177664), by norm_num⟩
  | 4 => ⟨((570957230929621/1125899906842624), (-64500756793607/2251799813685248)), (18798131/2251799813685248), by norm_num⟩
  | 5 => ⟨((577230836718605/2251799813685248), (-65418201507837/2251799813685248)), (20142423/2251799813685248), by norm_num⟩
  | 6 => ⟨((1168544009183637/18014398509481984), (-268310907308909/18014398509481984)), (91976269/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-1694202921/33554432)), (1/16777216), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-862947319/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((111114600496797/4503599627370496), (-1049456617779395/18014398509481984)), (39964849/4503599627370496), by norm_num⟩
  | 1 => ⟨((-624027559/8589934592), (1473455893/8589934592)), (227/8589934592), by norm_num⟩
  | 2 => ⟨((459352767/4294967296), (-1084625241/4294967296)), (169/4294967296), by norm_num⟩
  | 3 => ⟨((-450845397/4294967296), (266134403/1073741824)), (21/536870912), by norm_num⟩
  | 4 => ⟨((165935845/2147483648), (-391808255/2147483648)), (125/4294967296), by norm_num⟩
  | 5 => ⟨((-48858797/1073741824), (922924399/8589934592)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((95907831/4294967296), (-905831525/17179869184)), (37/4294967296), by norm_num⟩
  | 7 => ⟨((-10085527/1073741824), (762047329/34359738368)), (63/17179869184), by norm_num⟩
  | 8 => ⟨((475139501/137438953472), (-560950465/68719476736)), (187/137438953472), by norm_num⟩
  | 9 => ⟨((-621786341/549755813888), (367040981/137438953472)), (247/549755813888), by norm_num⟩
  | 10 => ⟨((91540597/274877906944), (-864583817/1099511627776)), (147/1099511627776), by norm_num⟩
  | 11 => ⟨((-196025965/2199023255552), (57857143/274877906944)), (159/4398046511104), by norm_num⟩
  | 12 => ⟨((384790995/17592186044416), (-56785609/1099511627776)), (79/8796093022208), by norm_num⟩
  | 13 => ⟨((-348613417/70368744177664), (823147129/70368744177664)), (145/70368744177664), by norm_num⟩
  | 14 => ⟨((586554819/562949953421312), (-692487569/281474976710656)), (123/281474976710656), by norm_num⟩
  | 15 => ⟨((-460553299/2251799813685248), (543729971/1125899906842624)), (195/2251799813685248), by norm_num⟩
  | 16 => ⟨((339017771/9007199254740992), (-200122465/2251799813685248)), (145/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (-1524297853683/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888855371462575/316912650057057350374175801344), (-1801885557945/633825300114114700748351602688)), (46189/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888551774572991/39614081257132168796771975168), (-1013319429401/19807040628566084398385987584)), (103937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888252721970457/2475880078570760549798248448), (-1076348827093/1237940039285380274899124224)), (55223/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884959628471781/77371252455336267181195264), (-1076008045205/77371252455336267181195264)), (110461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774180881286581/4835703278458516698824704), (-504197802641/2417851639229258349412352)), (103573/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157218285229705/75557863725914323419136), (-1763968758387/604462909807314587353088)), (90643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886098710358687/75557863725914323419136), (-1432546630639/37778931862957161709568)), (147323/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296269949071783/4722366482869645213696), (-1073817078811/2361183241434822606848)), (110519/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619703352705659/590295810358705651712), (-2951071346831/590295810358705651712)), (152005/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910647437154729/36893488147419103232), (-1842976501419/36893488147419103232)), (95035/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820206328393593/9223372036854775808), (-1035683070393/2305843009213693952)), (53479/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795728443223185/576460752303423488), (-4137781695779/1152921504606846976)), (214025/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192370217206309/144115188075855872), (-3614997090875/144115188075855872)), (46849/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488326193308567/36028797018963968), (-5411390614961/36028797018963968)), (70335/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485126730794945/9007199254740992), (-6744846630899/9007199254740992)), (88027/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219710331833229/4503599627370496), (-13431686594237/4503599627370496)), (705521/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101903689788575/1125899906842624), (-156274222657/17592186044416)), (530777/1125899906842624), by norm_num⟩
  | 0 => ⟨((2156380709790095/2251799813685248), (-39431994468389/2251799813685248)), (1068141/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2156380709790095/2251799813685248), (-39431994468389/2251799813685248)), (4074634556296920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516078611330859/562949953421312), (-75522159388605/2251799813685248)), (4166335/2251799813685248), by norm_num⟩
  | 2 => ⟨((1889906245994183/2251799813685248), (-138468334192435/2251799813685248)), (7918357/2251799813685248), by norm_num⟩
  | 3 => ⟨((1577658954176629/2251799813685248), (-58107334424727/562949953421312)), (14265385/2251799813685248), by norm_num⟩
  | 4 => ⟨((1081350288721047/2251799813685248), (-162844949007213/1125899906842624)), (22934195/2251799813685248), by norm_num⟩
  | 5 => ⟨((472175426424057/2251799813685248), (-312802997061315/2251799813685248)), (28660927/2251799813685248), by norm_num⟩
  | 6 => ⟨((111114600496797/4503599627370496), (-1049456617779395/18014398509481984)), (39964849/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-862947319/16777216)), (1/16777216), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-1755960407/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-258186724825457/9007199254740992), (-59724568947165/1125899906842624)), (49013137/4503599627370496), by norm_num⟩
  | 1 => ⟨((92203415/1073741824), (1365042257/8589934592)), (283/8589934592), by norm_num⟩
  | 2 => ⟨((-138108373/1073741824), (-511162643/2147483648)), (107/2147483648), by norm_num⟩
  | 3 => ⟨((275823807/2147483648), (1020870951/4294967296)), (27/536870912), by norm_num⟩
  | 4 => ⟨((-103286785/1073741824), (-382282007/2147483648)), (163/4294967296), by norm_num⟩
  | 5 => ⟨((61883911/1073741824), (916171637/8589934592)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((-123591753/4294967296), (-457434157/8589934592)), (199/17179869184), by norm_num⟩
  | 7 => ⟨((423140347/34359738368), (48941081/2147483648)), (43/8589934592), by norm_num⟩
  | 8 => ⟨((-633807597/137438953472), (-1172915007/137438953472)), (259/137438953472), by norm_num⟩
  | 9 => ⟨((421937305/274877906944), (780830965/274877906944)), (87/137438953472), by norm_num⟩
  | 10 => ⟨((-505604481/1099511627776), (-935664209/1099511627776)), (105/549755813888), by norm_num⟩
  | 11 => ⟨((550783877/4398046511104), (509636267/2199023255552)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((-550000345/17592186044416), (-508911271/8796093022208)), (29/2199023255552), by norm_num⟩
  | 13 => ⟨((506970395/70368744177664), (469095975/35184372088832)), (27/8796093022208), by norm_num⟩
  | 14 => ⟨((-216963939/140737488355328), (-3136799/1099511627776)), (187/281474976710656), by norm_num⟩
  | 15 => ⟨((693296933/2251799813685248), (1283005099/2251799813685248)), (301/2251799813685248), by norm_num⟩
  | 16 => ⟨((-519232999/9007199254740992), (-480442473/4503599627370496)), (57/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (-1345738316509/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777633010477917/633825300114114700748351602688), (-397670601421/79228162514264337593543950336)), (46257/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944232072755779/19807040628566084398385987584), (-1789081230937/19807040628566084398385987584)), (52049/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888159371095175/2475880078570760549798248448), (-475088499209/309485009821345068724781056)), (27657/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769825630810033/154742504910672534362390528), (-3799482653255/154742504910672534362390528)), (55327/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96767105992393/604462909807314587353088), (-3560713522685/9671406556917033397649408)), (103767/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4912769264007/2361183241434822606848), (-1557161692161/302231454903657293676544)), (11353/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885972469537317/75557863725914323419136), (-5058337319637/75557863725914323419136)), (18455/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648087395382335/2361183241434822606848), (-3791620679593/4722366482869645213696)), (13847/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619571734980925/590295810358705651712), (-5210015486995/590295810358705651712)), (19049/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821129191664729/73786976294838206464), (-6507328534801/73786976294838206464)), (95301/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820018343137751/9223372036854775808), (-1828403265259/2305843009213693952)), (214581/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591266915919519/1152921504606846976), (-1826176848291/288230376151711744)), (214773/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192201766537351/144115188075855872), (-6381612125727/144115188075855872)), (11759/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488069081781307/36028797018963968), (-9552434557537/36028797018963968)), (141325/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484797618247905/9007199254740992), (-11905639392901/9007199254740992)), (354075/9007199254740992), by norm_num⟩
  | 2 => ⟨((554757273230909/1125899906842624), (-23706837201933/4503599627370496)), (355221/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202728528949629/2251799813685248), (-17650047281415/1125899906842624)), (1071413/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153998274643339/2251799813685248), (-2173912095297/70368744177664)), (1082967/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2153998274643339/2251799813685248), (-2173912095297/70368744177664)), (4131191257957076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1029147711921141/1125899906842624), (-33271894768177/562949953421312)), (2138775/1125899906842624), by norm_num⟩
  | 2 => ⟨((1873553644718593/2251799813685248), (-60825467990267/562949953421312)), (2081391/562949953421312), by norm_num⟩
  | 3 => ⟨((1532555175537881/2251799813685248), (-404866459450939/2251799813685248)), (1956659/281474976710656), by norm_num⟩
  | 4 => ⟨((121281235947435/281474976710656), (-551097112684959/2251799813685248)), (26935777/2251799813685248), by norm_num⟩
  | 5 => ⟨((566370787370025/4503599627370496), (-949821397760711/4503599627370496)), (72792731/4503599627370496), by norm_num⟩
  | 6 => ⟨((-258186724825457/9007199254740992), (-59724568947165/1125899906842624)), (49013137/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-1755960407/33554432)), (1/16777216), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-1784558957/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1011911867342415/18014398509481984), (-229551307892535/18014398509481984)), (180252535/18014398509481984), by norm_num⟩
  | 1 => ⟨((1469034379/8589934592), (333249143/8589934592)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((-139765879/536870912), (-253646123/4294967296)), (203/4294967296), by norm_num⟩
  | 3 => ⟨((567360473/2147483648), (128705219/2147483648)), (13/268435456), by norm_num⟩
  | 4 => ⟨((-1727341691/8589934592), (-391845927/8589934592)), (319/8589934592), by norm_num⟩
  | 5 => ⟨((1051786107/8589934592), (238596743/8589934592)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((-266848867/4294967296), (-242137713/17179869184)), (201/17179869184), by norm_num⟩
  | 7 => ⟨((928488415/34359738368), (52656693/8589934592)), (177/34359738368), by norm_num⟩
  | 8 => ⟨((-1413401907/137438953472), (-320628967/137438953472)), (17/8589934592), by norm_num⟩
  | 9 => ⟨((119531495/34359738368), (54231227/68719476736)), (93/137438953472), by norm_num⟩
  | 10 => ⟨((-291133055/274877906944), (-66043275/274877906944)), (57/274877906944), by norm_num⟩
  | 11 => ⟨((161156567/549755813888), (292465793/4398046511104)), (127/2199023255552), by norm_num⟩
  | 12 => ⟨((-1308386091/17592186044416), (-296806223/17592186044416)), (65/4398046511104), by norm_num⟩
  | 13 => ⟨((1225664865/70368744177664), (139020493/35184372088832)), (123/35184372088832), by norm_num⟩
  | 14 => ⟨((-1066161195/281474976710656), (-30232215/35184372088832)), (27/35184372088832), by norm_num⟩
  | 15 => ⟨((865587115/1125899906842624), (49089417/281474976710656)), (353/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1317649697/9007199254740992), (-298907663/9007199254740992)), (135/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (-950424180045/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888778590666377/316912650057057350374175801344), (-561665198197/79228162514264337593543950336)), (92643/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888378565091953/39614081257132168796771975168), (-631714991501/4951760157141521099596496896)), (26063/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236008508827845/309485009821345068724781056), (-2684005860363/1237940039285380274899124224)), (110801/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769733913177039/154742504910672534362390528), (-5366250736247/154742504910672534362390528)), (55419/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548187267772917/9671406556917033397649408), (-314311847247/604462909807314587353088)), (103951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314398216157227/151115727451828646838272), (-4398495955049/604462909807314587353088)), (22749/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885848032274925/75557863725914323419136), (-7144051133587/75557863725914323419136)), (73971/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296080738893191/4722366482869645213696), (-5354972937187/4722366482869645213696)), (55511/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809720619553849/295147905179352825856), (-459881805927/36893488147419103232)), (19095/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910482156596787/36893488147419103232), (-4595085991053/36893488147419103232)), (47777/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227478805241059/1152921504606846976), (-10328687124537/9223372036854775808)), (107607/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591076006318203/1152921504606846976), (-161185577021/18014398509481984)), (107743/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192031346861583/144115188075855872), (-4505997468409/72057594037927936)), (188857/144115188075855872), by norm_num⟩
  | 4 => ⟨((185975841416825/4503599627370496), (-13489232888195/36028797018963968)), (70975/9007199254740992), by norm_num⟩
  | 3 => ⟨((742228989152995/4503599627370496), (-4202822810627/2251799813685248)), (355951/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218314945701711/4503599627370496), (-33472150061995/4503599627370496)), (715137/4503599627370496), by norm_num⟩
  | 1 => ⟨((275196371348413/281474976710656), (-12458313574577/562949953421312)), (135103/281474976710656), by norm_num⟩
  | 0 => ⟨((1075671385253663/1125899906842624), (-49086643970361/1125899906842624)), (1097137/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1075671385253663/1125899906842624), (-49086643970361/1125899906842624)), (4185245518210982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2051087176435227/2251799813685248), (-187587184246679/2251799813685248)), (2192049/1125899906842624), by norm_num⟩
  | 2 => ⟨((926318944581491/1125899906842624), (-341733457595655/2251799813685248)), (272409/70368744177664), by norm_num⟩
  | 3 => ⟨((1472371288145697/2251799813685248), (-562313175166535/2251799813685248)), (16989547/2251799813685248), by norm_num⟩
  | 4 => ⟨((822311598009917/2251799813685248), (-11489889235345/35184372088832)), (30702879/2251799813685248), by norm_num⟩
  | 5 => ⟨((30076488058783/1125899906842624), (-1074143844797787/4503599627370496)), (42476943/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1011911867342415/18014398509481984), (-229551307892535/18014398509481984)), (180252535/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-1784558957/33554432)), (1/16777216), by norm_num⟩, -8, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile006Terms2

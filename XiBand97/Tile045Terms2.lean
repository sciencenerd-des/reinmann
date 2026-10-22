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
namespace Reinmann.XiBand97.Tile045Terms2
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
  | 0 => ⟨((-20060163/8388608), (-1325896821/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-363652645748725/4503599627370496), (775484727325031/18014398509481984)), (594552237/18014398509481984), by norm_num⟩
  | 1 => ⟨((961550927/4294967296), (-512623837/4294967296)), (395/4294967296), by norm_num⟩
  | 2 => ⟨((-333248157/1073741824), (710647535/4294967296)), (275/2147483648), by norm_num⟩
  | 3 => ⟨((153993347/536870912), (-164194445/1073741824)), (511/4294967296), by norm_num⟩
  | 4 => ⟨((-426960217/2147483648), (227621833/2147483648)), (357/4294967296), by norm_num⟩
  | 5 => ⟨((473514033/4294967296), (-252440691/4294967296)), (199/4294967296), by norm_num⟩
  | 6 => ⟨((-875239779/17179869184), (466609475/17179869184)), (185/8589934592), by norm_num⟩
  | 7 => ⟨((346668563/17179869184), (-369633191/34359738368)), (589/68719476736), by norm_num⟩
  | 8 => ⟨((-240292337/34359738368), (64052551/17179869184)), (205/68719476736), by norm_num⟩
  | 9 => ⟨((1184412131/549755813888), (-157859005/137438953472)), (507/549755813888), by norm_num⟩
  | 10 => ⟨((-1313555087/2199023255552), (700284955/2199023255552)), (141/549755813888), by norm_num⟩
  | 11 => ⟨((1324344735/8796093022208), (-22063661/274877906944)), (571/8796093022208), by norm_num⟩
  | 12 => ⟨((-611977213/17592186044416), (326258441/17592186044416)), (265/17592186044416), by norm_num⟩
  | 13 => ⟨((1044160689/140737488355328), (-556664907/140737488355328)), (227/70368744177664), by norm_num⟩
  | 14 => ⟨((-206787725/140737488355328), (440972241/562949953421312)), (361/562949953421312), by norm_num⟩
  | 15 => ⟨((305779901/1125899906842624), (-163017955/1125899906842624)), (67/562949953421312), by norm_num⟩
  | 16 => ⟨((-847801905/18014398509481984), (28248859/1125899906842624)), (373/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (863566383595/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889135996101345/316912650057057350374175801344), (4085806758095/633825300114114700748351602688)), (46301/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472295659089875/9903520314283042199192993792), (2297778802579/19807040628566084398385987584)), (208407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888922305510853/2475880078570760549798248448), (4881586751703/2475880078570760549798248448)), (55373/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770588045616865/154742504910672534362390528), (4880244619515/154742504910672534362390528)), (27695/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548987907939001/9671406556917033397649408), (4573803626177/9671406556917033397649408)), (207783/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629146657807285/302231454903657293676544), (4000652817457/604462909807314587353088)), (181883/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943493030052755/37778931862957161709568), (1624597257257/18889465931478580854784)), (295693/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296934080026459/4722366482869645213696), (4871454689623/4722366482869645213696)), (3467/73786976294838206464), by norm_num⟩
  | 9 => ⟨((405153572610259/147573952589676412928), (6694453831823/590295810358705651712)), (305287/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56950943348167/2305843009213693952), (4181187588471/36893488147419103232)), (381895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910739471492183/4611686018427387904), (4699924689927/4611686018427387904)), (430027/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592723745711075/1152921504606846976), (9390076955573/1152921504606846976)), (430521/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596736129099579/72057594037927936), (8205331534417/144115188075855872)), (377263/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489966367715273/36028797018963968), (3071511536787/9007199254740992)), (17719/1125899906842624), by norm_num⟩
  | 3 => ⟨((1487154474222105/9007199254740992), (15319189200789/9007199254740992)), (88839/1125899906842624), by norm_num⟩
  | 2 => ⟨((555924676376979/1125899906842624), (7630864308763/1125899906842624)), (356823/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104811620508129/1125899906842624), (2843658032711/140737488355328)), (538911/562949953421312), by norm_num⟩
  | 0 => ⟨((1083676057438767/1125899906842624), (44927152980221/1125899906842624)), (2185179/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083676057438767/1125899906842624), (44927152980221/1125899906842624)), (8335796360496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((520621478546311/562949953421312), (86484561758401/1125899906842624)), (1095213/281474976710656), by norm_num⟩
  | 2 => ⟨((1912616405292847/2251799813685248), (159963492812979/1125899906842624)), (8775927/1125899906842624), by norm_num⟩
  | 3 => ⟨((789534712644895/1125899906842624), (67934280556969/281474976710656)), (17401759/1125899906842624), by norm_num⟩
  | 4 => ⟨((976150713815417/2251799813685248), (381110060333499/1125899906842624)), (32805753/1125899906842624), by norm_num⟩
  | 5 => ⟨((82576324385627/1125899906842624), (1321683589014745/4503599627370496)), (202606165/4503599627370496), by norm_num⟩
  | 6 => ⟨((-363652645748725/4503599627370496), (775484727325031/18014398509481984)), (594552237/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1325896821/16777216)), (1/8388608), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1354888497/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((117884746190179/2251799813685248), (1248223313629877/18014398509481984)), (387079643/18014398509481984), by norm_num⟩
  | 1 => ⟨((-318520199/2147483648), (-105395405/536870912)), (33/536870912), by norm_num⟩
  | 2 => ⟨((451217839/2147483648), (1194430671/4294967296)), (377/4294967296), by norm_num⟩
  | 3 => ⟨((-213066067/1073741824), (-1128025639/4294967296)), (359/4294967296), by norm_num⟩
  | 4 => ⟨((75457703/536870912), (798984323/4294967296)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-684120867/8589934592), (-452738609/4294967296)), (73/2147483648), by norm_num⟩
  | 6 => ⟨((323043395/8589934592), (106892089/2147483648)), (139/8589934592), by norm_num⟩
  | 7 => ⟨((-261500245/17179869184), (-173056053/8589934592)), (227/34359738368), by norm_num⟩
  | 8 => ⟨((23152687/4294967296), (980609437/137438953472)), (81/34359738368), by norm_num⟩
  | 9 => ⟨((-466464013/274877906944), (-617394609/274877906944)), (103/137438953472), by norm_num⟩
  | 10 => ⟨((264318413/549755813888), (349842129/549755813888)), (235/1099511627776), by norm_num⟩
  | 11 => ⟨((-272316529/2199023255552), (-360428141/2199023255552)), (61/1099511627776), by norm_num⟩
  | 12 => ⟨((514353883/17592186044416), (680779879/17592186044416)), (29/2199023255552), by norm_num⟩
  | 13 => ⟨((-896784175/140737488355328), (-593475273/70368744177664)), (407/140737488355328), by norm_num⟩
  | 14 => ⟨((362968699/281474976710656), (240206009/140737488355328)), (83/140737488355328), by norm_num⟩
  | 15 => ⟨((-274231403/1125899906842624), (-725925195/2251799813685248)), (253/2251799813685248), by norm_num⟩
  | 16 => ⟨((388478035/9007199254740992), (1028350475/18014398509481984)), (361/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (601651193625/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222274911345519/79228162514264337593543950336), (711589263469/316912650057057350374175801344)), (23085/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889101302542143/39614081257132168796771975168), (1600736480055/39614081257132168796771975168)), (25973/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888836488740321/2475880078570760549798248448), (1700358658711/2475880078570760549798248448)), (220791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770502903682343/154742504910672534362390528), (1699882031601/154742504910672534362390528)), (220815/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774454401936853/4835703278458516698824704), (99570823033/604462909807314587353088)), (207039/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629112407738221/302231454903657293676544), (1393485489151/604462909807314587353088)), (2831/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1886876088498835/75557863725914323419136), (1131732769069/37778931862957161709568)), (147235/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324213193392485/1180591620717411303424), (1696769750097/4722366482869645213696)), (110447/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202563049582915/73786976294838206464), (2331711432429/590295810358705651712)), (75949/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822295669790863/73786976294838206464), (2912620240479/73786976294838206464)), (379845/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910665761499385/4611686018427387904), (3273923867655/9223372036854775808)), (53433/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592581205968677/1152921504606846976), (408807490305/144115188075855872)), (427637/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193353012742251/144115188075855872), (1428880104885/72057594037927936)), (46797/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489798419578325/36028797018963968), (2139433822603/18014398509481984)), (561955/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486963573710031/9007199254740992), (5335008838925/9007199254740992)), (703127/9007199254740992), by norm_num⟩
  | 2 => ⟨((555843426870833/1125899906842624), (10629396139065/4503599627370496)), (704155/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209276701313447/2251799813685248), (3960727275937/562949953421312)), (529407/562949953421312), by norm_num⟩
  | 0 => ⟨((2167216589840371/2251799813685248), (1955205187687/140737488355328)), (2128015/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167216589840371/2251799813685248), (1955205187687/140737488355328)), (8117733006003951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042687958970641/1125899906842624), (60216409555341/2251799813685248)), (8310581/2251799813685248), by norm_num⟩
  | 2 => ⟨((1929641647868555/2251799813685248), (55765991980471/1125899906842624)), (494913/70368744177664), by norm_num⟩
  | 3 => ⟨((206006184652197/281474976710656), (191150882962569/2251799813685248)), (7177927/562949953421312), by norm_num⟩
  | 4 => ⟨((74371853656101/140737488355328), (139899697487129/1125899906842624)), (46901669/2251799813685248), by norm_num⟩
  | 5 => ⟨((1188109600330229/4503599627370496), (591433026104685/4503599627370496)), (122450823/4503599627370496), by norm_num⟩
  | 6 => ⟨((117884746190179/2251799813685248), (1248223313629877/18014398509481984)), (387079643/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1354888497/16777216)), (1/8388608), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-86388911/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1133716634514763/18014398509481984), (-965579563148253/18014398509481984)), (81188589/4503599627370496), by norm_num⟩
  | 1 => ⟨((-781264911/4294967296), (332699287/2147483648)), (113/2147483648), by norm_num⟩
  | 2 => ⟨((1129073017/4294967296), (-961624623/4294967296)), (329/4294967296), by norm_num⟩
  | 3 => ⟨((-1087813587/4294967296), (463242109/2147483648)), (319/4294967296), by norm_num⟩
  | 4 => ⟨((393023209/2147483648), (-669470955/4294967296)), (233/4294967296), by norm_num⟩
  | 5 => ⟨((-908786547/8589934592), (774007977/8589934592)), (271/8589934592), by norm_num⟩
  | 6 => ⟨((437788495/8589934592), (-745723599/17179869184)), (263/17179869184), by norm_num⟩
  | 7 => ⟨((-361534715/17179869184), (615833837/34359738368)), (219/34359738368), by norm_num⟩
  | 8 => ⟨((522484865/68719476736), (-889994365/137438953472)), (159/68719476736), by norm_num⟩
  | 9 => ⟨((-335594555/137438953472), (142911921/68719476736)), (103/137438953472), by norm_num⟩
  | 10 => ⟨((775994419/1099511627776), (-660909729/1099511627776)), (15/68719476736), by norm_num⟩
  | 11 => ⟨((-203901123/1099511627776), (694645387/4398046511104)), (127/2199023255552), by norm_num⟩
  | 12 => ⟨((785800063/17592186044416), (-41828821/1099511627776)), (247/17592186044416), by norm_num⟩
  | 13 => ⟨((-87355935/8796093022208), (297602075/35184372088832)), (221/70368744177664), by norm_num⟩
  | 14 => ⟨((577122577/281474976710656), (-245765895/140737488355328)), (367/562949953421312), by norm_num⟩
  | 15 => ⟨((-222413173/562949953421312), (757711789/2251799813685248)), (285/2251799813685248), by norm_num⟩
  | 16 => ⟨((321428377/4503599627370496), (-547517189/9007199254740992)), (207/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-918962103073/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778123794247827/633825300114114700748351602688), (-1086793039203/633825300114114700748351602688)), (92307/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889016412318709/39614081257132168796771975168), (-1222378419007/39614081257132168796771975168)), (207705/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888746348915883/2475880078570760549798248448), (-324611730163/618970019642690137449562112)), (110351/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442603206712681/38685626227668133590597632), (-324518918135/38685626227668133590597632)), (13795/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548824423734811/9671406556917033397649408), (-38017238693/302231454903657293676544)), (6467/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258151049701611/604462909807314587353088), (-133011067901/75557863725914323419136)), (22637/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943378172179383/37778931862957161709568), (-1728405219523/75557863725914323419136)), (73579/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324190768739987/1180591620717411303424), (-1295657933841/4722366482869645213696)), (220769/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620381238828945/590295810358705651712), (-1780480595121/590295810358705651712)), (37951/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822141988823291/73786976294838206464), (-1112014146647/36893488147419103232)), (379587/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821158997610719/9223372036854775808), (-2499871569909/9223372036854775808)), (106785/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592409136961727/1152921504606846976), (-2497174031531/1152921504606846976)), (427273/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193202964767779/144115188075855872), (-1090998187165/72057594037927936)), (374013/144115188075855872), by norm_num⟩
  | 4 => ⟨((744787184939553/18014398509481984), (-1633471155363/18014398509481984)), (280659/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486685294818837/9007199254740992), (-4073107914869/9007199254740992)), (702173/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222822476556305/4503599627370496), (-8114591594995/4503599627370496)), (351481/1125899906842624), by norm_num⟩
  | 1 => ⟨((276057886549127/281474976710656), (-3023281479657/562949953421312)), (1056427/1125899906842624), by norm_num⟩
  | 0 => ⟨((2165641846124597/2251799813685248), (-11936497167455/1125899906842624)), (1060425/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165641846124597/2251799813685248), (-11936497167455/1125899906842624)), (4045200350047874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((260315918034073/281474976710656), (-11479785016805/562949953421312)), (8248749/2251799813685248), by norm_num⟩
  | 2 => ⟨((1925043045955425/2251799813685248), (-21233651462775/562949953421312)), (1949221/281474976710656), by norm_num⟩
  | 3 => ⟨((1642498067116031/2251799813685248), (-18152454245815/281474976710656)), (1739893/140737488355328), by norm_num⟩
  | 4 => ⟨((1188698543326495/2251799813685248), (-211850952866849/2251799813685248)), (44201977/2251799813685248), by norm_num⟩
  | 5 => ⟨((1215137679967117/4503599627370496), (-223667235022121/2251799813685248)), (54984513/2251799813685248), by norm_num⟩
  | 6 => ⟨((1133716634514763/18014398509481984), (-965579563148253/18014398509481984)), (81188589/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-86388911/1048576)), (1/8388608), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-352019599/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-222270134148885/4503599627370496), (-1108924478305645/18014398509481984)), (129762889/4503599627370496), by norm_num⟩
  | 1 => ⟨((624142501/4294967296), (778474917/4294967296)), (183/2147483648), by norm_num⟩
  | 2 => ⟨((-459437377/2147483648), (-1146085945/4294967296)), (541/4294967296), by norm_num⟩
  | 3 => ⟨((901856881/4294967296), (1124860043/4294967296)), (533/4294967296), by norm_num⟩
  | 4 => ⟨((-331932819/2147483648), (-828020439/4294967296)), (197/2147483648), by norm_num⟩
  | 5 => ⟨((781884745/8589934592), (487611131/4294967296)), (467/8589934592), by norm_num⟩
  | 6 => ⟨((-767403973/17179869184), (-478580407/8589934592)), (461/17179869184), by norm_num⟩
  | 7 => ⟨((161398155/8589934592), (805229031/34359738368)), (195/17179869184), by norm_num⟩
  | 8 => ⟨((-950454037/137438953472), (-1185473873/137438953472)), (577/137438953472), by norm_num⟩
  | 9 => ⟨((310950435/137438953472), (193919749/68719476736)), (379/274877906944), by norm_num⟩
  | 10 => ⟨((-732459665/1099511627776), (-228393947/274877906944)), (7/17179869184), by norm_num⟩
  | 11 => ⟨((784248287/4398046511104), (7641955/34359738368)), (241/2199023255552), by norm_num⟩
  | 12 => ⟨((-384861871/8796093022208), (-480027097/8796093022208)), (475/17592186044416), by norm_num⟩
  | 13 => ⟨((348677629/35184372088832), (434895537/35184372088832)), (27/4398046511104), by norm_num⟩
  | 14 => ⟨((-293331429/140737488355328), (-731727641/281474976710656)), (365/281474976710656), by norm_num⟩
  | 15 => ⟨((230319065/562949953421312), (574540637/1125899906842624)), (9/35184372088832), by norm_num⟩
  | 16 => ⟨((-678160433/9007199254740992), (-845849923/9007199254740992)), (213/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-2926452044629/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889023085586631/316912650057057350374175801344), (-3460646265819/633825300114114700748351602688)), (92541/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888928785352441/39614081257132168796771975168), (-3892359740799/39614081257132168796771975168)), (208261/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888652842964767/2475880078570760549798248448), (-4134559849855/2475880078570760549798248448)), (13833/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885159434405325/77371252455336267181195264), (-2066676888119/77371252455336267181195264)), (221385/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774367929056581/4835703278458516698824704), (-3873738081581/9671406556917033397649408)), (207609/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258073075257423/604462909807314587353088), (-1694120076609/302231454903657293676544)), (181719/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886628737698399/75557863725914323419136), (-5503489878925/75557863725914323419136)), (147703/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296666584970257/4722366482869645213696), (-4125517967995/4722366482869645213696)), (221655/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6329090981257/2305843009213693952), (-5669177268589/590295810358705651712)), (304937/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821972646467435/73786976294838206464), (-7081359574417/73786976294838206464)), (381415/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910482934549599/4611686018427387904), (-1989876302111/2305843009213693952)), (214713/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99513296426871/72057594037927936), (-3975365934739/576460752303423488)), (429845/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193027456144303/144115188075855872), (-1736757518103/36028797018963968)), (376587/144115188075855872), by norm_num⟩
  | 4 => ⟨((372325951135485/9007199254740992), (-10400848703577/36028797018963968)), (565823/36028797018963968), by norm_num⟩
  | 3 => ⟨((743167182660761/4503599627370496), (-12966646640091/9007199254740992)), (354467/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222082673946595/4503599627370496), (-12915134146089/2251799813685248)), (711421/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207259313550359/2251799813685248), (-38488601356641/2251799813685248)), (134171/140737488355328), by norm_num⟩
  | 0 => ⟨((1081431335084701/1125899906842624), (-2373580042289/70368744177664)), (2171787/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081431335084701/1125899906842624), (-2373580042289/70368744177664)), (8284709934714889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2074876197354115/2251799813685248), (-72954658039151/1125899906842624)), (1079633/281474976710656), by norm_num⟩
  | 2 => ⟨((29724984319997/35184372088832), (-268890480462047/2251799813685248)), (8518105/1125899906842624), by norm_num⟩
  | 3 => ⟨((196888053156889/281474976710656), (-56792013335857/281474976710656)), (32854203/2251799813685248), by norm_num⟩
  | 4 => ⟨((1010095408479679/2251799813685248), (-635604291150967/2251799813685248)), (14804969/562949953421312), by norm_num⟩
  | 5 => ⟨((136846072096787/1125899906842624), (-570229175968227/2251799813685248)), (21640053/562949953421312), by norm_num⟩
  | 6 => ⟨((-222270134148885/4503599627370496), (-1108924478305645/18014398509481984)), (129762889/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-352019599/4194304)), (1/8388608), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-22384495/262144)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-286744665238641/4503599627370496), (730445145027899/18014398509481984)), (247718777/9007199254740992), by norm_num⟩
  | 1 => ⟨((819216011/4294967296), (-521711849/4294967296)), (355/4294967296), by norm_num⟩
  | 2 => ⟨((-613537961/2147483648), (48840907/268435456)), (267/2147483648), by norm_num⟩
  | 3 => ⟨((612665157/2147483648), (-390171417/2147483648)), (535/4294967296), by norm_num⟩
  | 4 => ⟨((-114711299/536870912), (584424553/4294967296)), (201/2147483648), by norm_num⟩
  | 5 => ⟨((549830945/4294967296), (-350155899/4294967296)), (483/8589934592), by norm_num⟩
  | 6 => ⟨((-549048769/8589934592), (21853611/536870912)), (121/4294967296), by norm_num⟩
  | 7 => ⟨((117485937/4294967296), (-149640155/8589934592)), (417/34359738368), by norm_num⟩
  | 8 => ⟨((-351956413/34359738368), (224140921/34359738368)), (157/34359738368), by norm_num⟩
  | 9 => ⟨((234303819/68719476736), (-149214709/68719476736)), (105/68719476736), by norm_num⟩
  | 10 => ⟨((-280764605/274877906944), (715211711/1099511627776)), (505/1099511627776), by norm_num⟩
  | 11 => ⟨((1223411765/4398046511104), (-194780255/1099511627776)), (69/549755813888), by norm_num⟩
  | 12 => ⟨((-610835685/8796093022208), (389006331/8796093022208)), (277/8796093022208), by norm_num⟩
  | 13 => ⟨((8797597/549755813888), (-358571945/35184372088832)), (513/70368744177664), by norm_num⟩
  | 14 => ⟨((-481924485/140737488355328), (613820313/281474976710656)), (441/281474976710656), by norm_num⟩
  | 15 => ⟨((384991129/562949953421312), (-245178843/562949953421312)), (177/562949953421312), by norm_num⟩
  | 16 => ⟨((-576665175/4503599627370496), (734490173/9007199254740992)), (133/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (3353602914105/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444494003746425/158456325028528675187087900672), (3965479430745/633825300114114700748351602688)), (185181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888849766943175/39614081257132168796771975168), (4460149464843/39614081257132168796771975168)), (208379/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472142189964277/618970019642690137449562112), (2368829040827/1237940039285380274899124224)), (221461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770234644071711/154742504910672534362390528), (592031419007/19342813113834066795298816)), (221527/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96791046692165/604462909807314587353088), (1109685347589/2417851639229258349412352)), (207751/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629001851453793/302231454903657293676544), (970601227899/151115727451828646838272)), (45463/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235814465793743/9444732965739290427392), (6306108047389/75557863725914323419136)), (295639/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296581580667111/4722366482869645213696), (4727132043675/4722366482869645213696)), (55461/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620130011488111/590295810358705651712), (6495828730133/590295810358705651712)), (76305/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910912724852509/36893488147419103232), (8113822285989/73786976294838206464)), (95451/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113799965840377/576460752303423488), (9119855152015/9223372036854775808)), (214957/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796022652835867/576460752303423488), (9109619102583/1152921504606846976)), (215197/576460752303423488), by norm_num⟩
  | 5 => ⟨((298219950756781/36028797018963968), (7959411609085/144115188075855872)), (377135/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489080042616565/36028797018963968), (1489516665745/4503599627370496)), (566785/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486050689090313/9007199254740992), (14855003278939/9007199254740992)), (710377/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221503480245371/4503599627370496), (14794875751993/2251799813685248)), (178307/562949953421312), by norm_num⟩
  | 1 => ⟨((1103180599879011/1125899906842624), (5510601540005/281474976710656)), (538495/562949953421312), by norm_num⟩
  | 0 => ⟨((2160950821052527/2251799813685248), (43487650166549/1125899906842624)), (272837/140737488355328), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2160950821052527/2251799813685248), (43487650166549/1125899906842624)), (1040790558398199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1035203866659353/1125899906842624), (83466276852783/1125899906842624)), (4357883/1125899906842624), by norm_num⟩
  | 2 => ⟨((1891252356811197/2251799813685248), (306970848859795/2251799813685248)), (1082475/140737488355328), by norm_num⟩
  | 3 => ⟨((386646756288989/562949953421312), (32227517397977/140737488355328)), (16907519/1125899906842624), by norm_num⟩
  | 4 => ⟨((7376205652199/17592186044416), (708306803583967/2251799813685248)), (61936497/2251799813685248), by norm_num⟩
  | 5 => ⟨((86537190423601/1125899906842624), (1187940290057455/4503599627370496)), (181805959/4503599627370496), by norm_num⟩
  | 6 => ⟨((-286744665238641/4503599627370496), (730445145027899/18014398509481984)), (247718777/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-22384495/262144)), (1/8388608), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1455939927/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((492044575777851/18014398509481984), (301842735763771/4503599627370496)), (183582513/9007199254740992), by norm_num⟩
  | 1 => ⟨((-357160747/4294967296), (-109549401/536870912)), (67/1073741824), by norm_num⟩
  | 2 => ⟨((271845977/2147483648), (667051219/2147483648)), (205/2147483648), by norm_num⟩
  | 3 => ⟨((-34485049/268435456), (-676950801/2147483648)), (419/4294967296), by norm_num⟩
  | 4 => ⟨((209981011/2147483648), (64405997/268435456)), (321/4294967296), by norm_num⟩
  | 5 => ⟨((-31964595/536870912), (-1254947219/8589934592)), (393/8589934592), by norm_num⟩
  | 6 => ⟨((519023609/17179869184), (159196457/2147483648)), (401/17179869184), by norm_num⟩
  | 7 => ⟨((-451479721/34359738368), (-1107833567/34359738368)), (351/34359738368), by norm_num⟩
  | 8 => ⟨((343635035/68719476736), (421603019/34359738368)), (269/68719476736), by norm_num⟩
  | 9 => ⟨((-464979811/274877906944), (-285239967/68719476736)), (183/137438953472), by norm_num⟩
  | 10 => ⟨((566256587/1099511627776), (21710487/17179869184)), (7/17179869184), by norm_num⟩
  | 11 => ⟨((-156725535/1099511627776), (-384570559/1099511627776)), (249/2199023255552), by norm_num⟩
  | 12 => ⟨((318102939/8796093022208), (780555797/8796093022208)), (255/8796093022208), by norm_num⟩
  | 13 => ⟨((-595982483/70368744177664), (-1462412085/70368744177664)), (15/2199023255552), by norm_num⟩
  | 14 => ⟨((518423441/281474976710656), (1272098973/281474976710656)), (105/70368744177664), by norm_num⟩
  | 15 => ⟨((-420893813/1125899906842624), (-1032782365/1125899906842624)), (343/1125899906842624), by norm_num⟩
  | 16 => ⟨((80088791/1125899906842624), (786082271/4503599627370496)), (263/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (771023741119/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444479462212099/158456325028528675187087900672), (1823272667483/633825300114114700748351602688)), (184759/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236098088980967/4951760157141521099596496896), (2050715816285/39614081257132168796771975168)), (207877/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888500146794091/2475880078570760549798248448), (2178302041817/2475880078570760549798248448)), (220897/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770166601889665/154742504910672534362390528), (1088822944583/77371252455336267181195264)), (220927/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774296781810187/4835703278458516698824704), (63776441247/302231454903657293676544)), (207151/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257949022948065/604462909807314587353088), (892521873713/302231454903657293676544)), (181289/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886428005724043/75557863725914323419136), (2899390574347/75557863725914323419136)), (294655/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324129195399007/1180591620717411303424), (2173401228445/4722366482869645213696)), (55261/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810021260843335/295147905179352825856), (1493286295617/295147905179352825856)), (304021/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910859248580887/36893488147419103232), (932609158883/18446744073709551616)), (190077/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820682439221207/9223372036854775808), (4192923265461/9223372036854775808)), (213925/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198991552093307/144115188075855872), (1047038950205/288230376151711744)), (53509/144115188075855872), by norm_num⟩
  | 5 => ⟨((298196413478519/36028797018963968), (457409969697/18014398509481984)), (93703/36028797018963968), by norm_num⟩
  | 4 => ⟨((744474022865189/18014398509481984), (5478223552261/36028797018963968)), (562717/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485901771129349/9007199254740992), (6829099600759/9007199254740992)), (44017/562949953421312), by norm_num⟩
  | 2 => ⟨((1110626802302589/2251799813685248), (850144538421/281474976710656)), (1411177/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103052665381637/1125899906842624), (2533035796971/281474976710656)), (1061687/1125899906842624), by norm_num⟩
  | 0 => ⟨((135056821873255/140737488355328), (19987517692135/1125899906842624)), (4273335/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((135056821873255/140737488355328), (19987517692135/1125899906842624)), (16301479348189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072977501201427/2251799813685248), (76723001047731/2251799813685248)), (8353421/2251799813685248), by norm_num⟩
  | 2 => ⟨((1905741920537071/2251799813685248), (2207193525125/35184372088832)), (15949335/2251799813685248), by norm_num⟩
  | 3 => ⟨((100250301703081/140737488355328), (239102816270173/2251799813685248)), (28997539/2251799813685248), by norm_num⟩
  | 4 => ⟨((558589025943127/1125899906842624), (85159006847637/562949953421312)), (23734609/1125899906842624), by norm_num⟩
  | 5 => ⟨((1005465840773169/4503599627370496), (675994537648785/4503599627370496)), (122926195/4503599627370496), by norm_num⟩
  | 6 => ⟨((492044575777851/18014398509481984), (301842735763771/4503599627370496)), (183582513/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1455939927/16777216)), (1/8388608), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨45,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile045Terms2

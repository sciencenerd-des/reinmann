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
namespace Reinmann.XiBand97.Tile034Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32547/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32547/1280))
  have he : value ((69/80), (32547/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1874672179/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((1053460672002511/9007199254740992), (3321471096273/35184372088832)), (13481509/562949953421312), by norm_num⟩
  | 1 => ⟨((-1103730049/4294967296), (-890871329/4294967296)), (229/4294967296), by norm_num⟩
  | 2 => ⟨((303142849/1073741824), (489361095/2147483648)), (1/16777216), by norm_num⟩
  | 3 => ⟨((-888097225/4294967296), (-358412075/2147483648)), (95/2147483648), by norm_num⟩
  | 4 => ⟨((975674525/8589934592), (196877955/2147483648)), (211/8589934592), by norm_num⟩
  | 5 => ⟨((-857510419/17179869184), (-692136131/17179869184)), (47/4294967296), by norm_num⟩
  | 6 => ⟨((78505957/4294967296), (506926173/34359738368)), (35/8589934592), by norm_num⟩
  | 7 => ⟨((-788549569/137438953472), (-636474655/137438953472)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((866310247/549755813888), (349619439/274877906944)), (99/274877906944), by norm_num⟩
  | 9 => ⟨((-105748787/274877906944), (-341418855/1099511627776)), (49/549755813888), by norm_num⟩
  | 10 => ⟨((185883067/2199023255552), (37508695/549755813888)), (175/8796093022208), by norm_num⟩
  | 11 => ⟨((-1188150817/70368744177664), (-479505609/35184372088832)), (141/35184372088832), by norm_num⟩
  | 12 => ⟨((13597053/4398046511104), (702387673/281474976710656)), (209/281474976710656), by norm_num⟩
  | 13 => ⟨((-1176646067/2251799813685248), (-949725205/2251799813685248)), (285/2251799813685248), by norm_num⟩
  | 14 => ⟨((738673045/9007199254740992), (298108509/4503599627370496)), (181/9007199254740992), by norm_num⟩
  | 15 => ⟨((-54101019/4503599627370496), (-349339383/36028797018963968)), (107/36028797018963968), by norm_num⟩
  | 16 => ⟨((950976709/576460752303423488), (383788539/288230376151711744)), (237/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (442290788535/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779045272407315/633825300114114700748351602688), (1047166450841/633825300114114700748351602688)), (138455/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890052879008311/39614081257132168796771975168), (588933160817/19807040628566084398385987584)), (38943/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472461837926103/618970019642690137449562112), (1251241029763/2475880078570760549798248448)), (82759/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442878389069897/38685626227668133590597632), (312742234251/38685626227668133590597632)), (41383/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549856067216647/9671406556917033397649408), (1172494360109/9671406556917033397649408)), (2425/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((629526723744141/302231454903657293676544), (1025643637025/604462909807314587353088)), (67907/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888222196732451/75557863725914323419136), (416532340443/18889465931478580854784)), (220723/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324465497105477/1180591620717411303424), (1249123358147/4722366482869645213696)), (41391/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621891472023559/590295810358705651712), (1716775273987/590295810358705651712)), (28461/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824028621773875/73786976294838206464), (1072407852787/36893488147419103232)), (284665/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455819966947353/2305843009213693952), (2411332782133/9223372036854775808)), (80081/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594528018934115/1152921504606846976), (1204676601661/576460752303423488)), (320419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195054752038189/144115188075855872), (263244891009/18014398509481984)), (140237/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492347587560035/36028797018963968), (197155880663/2251799813685248)), (420925/36028797018963968), by norm_num⟩
  | 3 => ⟨((372536004763903/2251799813685248), (7686233115/17592186044416)), (131633/2251799813685248), by norm_num⟩
  | 2 => ⟨((69678643202395/140737488355328), (7847451040981/4503599627370496)), (1054193/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109373036595861/1125899906842624), (11713211944447/2251799813685248)), (792061/1125899906842624), by norm_num⟩
  | 0 => ⟨((68311755078053/70368744177664), (5798887554027/562949953421312)), (3179633/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((68311755078053/70368744177664), (5798887554027/562949953421312)), (12129337319380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((530459426324273/562949953421312), (2814688473875/140737488355328)), (3119441/1125899906842624), by norm_num⟩
  | 2 => ⟨((999237824704115/1125899906842624), (42435830014633/1125899906842624)), (3001791/562949953421312), by norm_num⟩
  | 3 => ⟨((885225608948997/1125899906842624), (150647446422651/2251799813685248)), (11108933/1125899906842624), by norm_num⟩
  | 4 => ⟨((86369879632809/140737488355328), (236889579056947/2251799813685248)), (18954933/1125899906842624), by norm_num⟩
  | 5 => ⟨((1646310546490263/4503599627370496), (9086120491293/70368744177664)), (109012857/4503599627370496), by norm_num⟩
  | 6 => ⟨((1053460672002511/9007199254740992), (3321471096273/35184372088832)), (13481509/562949953421312), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1874672179/33554432)), (3/33554432), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-982282889/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-257195622907967/4503599627370496), (-1124099341744069/9007199254740992)), (163737639/4503599627370496), by norm_num⟩
  | 1 => ⟨((141195013/1073741824), (617107007/2147483648)), (181/2147483648), by norm_num⟩
  | 2 => ⟨((-81278383/536870912), (-1420941395/4294967296)), (105/1073741824), by norm_num⟩
  | 3 => ⟨((499067715/4294967296), (1090612825/4294967296)), (81/1073741824), by norm_num⟩
  | 4 => ⟨((-574572941/8589934592), (-1255614417/8589934592)), (47/1073741824), by norm_num⟩
  | 5 => ⟨((132300309/4294967296), (1129359/16777216)), (349/17179869184), by norm_num⟩
  | 6 => ⟨((-406176959/34359738368), (-221904657/8589934592)), (135/17179869184), by norm_num⟩
  | 7 => ⟨((267216289/68719476736), (1167895669/137438953472)), (179/68719476736), by norm_num⟩
  | 8 => ⟨((-153822061/137438953472), (-1344589579/549755813888)), (415/549755813888), by norm_num⟩
  | 9 => ⟨((629668239/2199023255552), (1376014187/2199023255552)), (427/2199023255552), by norm_num⟩
  | 10 => ⟨((-72493235/1099511627776), (-633677951/4398046511104)), (99/2199023255552), by norm_num⟩
  | 11 => ⟨((242795407/17592186044416), (265290437/8796093022208)), (167/17592186044416), by norm_num⟩
  | 12 => ⟨((-372704723/140737488355328), (-814471741/140737488355328)), (129/70368744177664), by norm_num⟩
  | 13 => ⟨((16503545/35184372088832), (1154086455/1125899906842624)), (23/70368744177664), by norm_num⟩
  | 14 => ⟨((-173718019/2251799813685248), (-189813019/1125899906842624)), (61/1125899906842624), by norm_num⟩
  | 15 => ⟨((213333611/18014398509481984), (932396007/36028797018963968)), (151/18014398509481984), by norm_num⟩
  | 16 => ⟨((-491218793/288230376151711744), (-1073460573/288230376151711744)), (175/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-651291139377/2535301200456458802993406410752)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778900651865421/633825300114114700748351602688), (-385440978315/79228162514264337593543950336)), (138755/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472472488167173/9903520314283042199192993792), (-867089174183/9903520314283042199192993792)), (156129/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889673944726549/2475880078570760549798248448), (-3684381437003/2475880078570760549798248448)), (5185/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((885669907306671/77371252455336267181195264), (-460442573805/19342813113834066795298816)), (165959/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774846414514367/4835703278458516698824704), (-863106521187/2417851639229258349412352)), (155627/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258910258957491/604462909807314587353088), (-3019979808489/604462909807314587353088)), (68107/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943994425038881/37778931862957161709568), (-76653019001/1180591620717411303424)), (221423/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297686396850977/4722366482869645213696), (-3677880617551/4722366482869645213696)), (83067/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621649089578105/590295810358705651712), (-631838397489/73786976294838206464)), (228543/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911862114734243/36893488147419103232), (-3157408693701/36893488147419103232)), (17865/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455733871195997/2305843009213693952), (-7099267804607/9223372036854775808)), (321793/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594181213241899/1152921504606846976), (-3546572030857/576460752303423488)), (40259/144115188075855872), by norm_num⟩
  | 5 => ⟨((597374288782387/72057594037927936), (-1549904147575/36028797018963968)), (17633/9007199254740992), by norm_num⟩
  | 4 => ⟨((745941450959029/18014398509481984), (-9285667825765/36028797018963968)), (105955/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489553703934755/9007199254740992), (-723939789391/562949953421312)), (530877/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114253856494177/2251799813685248), (-23094035615097/4503599627370496)), (1065065/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216862641890705/2251799813685248), (-4307666643227/281474976710656)), (1605893/2251799813685248), by norm_num⟩
  | 0 => ⟨((2181931607467239/2251799813685248), (-34103014094483/1125899906842624)), (405635/281474976710656), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2181931607467239/2251799813685248), (-34103014094483/1125899906842624)), (1547374726415538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2112165321480955/2251799813685248), (-132179501766411/2251799813685248)), (3242685/1125899906842624), by norm_num⟩
  | 2 => ⟨((1973430718651205/2251799813685248), (-123983028218097/1125899906842624)), (12927799/2251799813685248), by norm_num⟩
  | 3 => ⟨((851084011304447/1125899906842624), (-434624632243071/2251799813685248)), (12753253/1125899906842624), by norm_num⟩
  | 4 => ⟨((1202805591233801/2251799813685248), (-82134760197839/281474976710656)), (48407603/2251799813685248), by norm_num⟩
  | 5 => ⟨((112686491805167/562949953421312), (-701960436804031/2251799813685248)), (79964935/2251799813685248), by norm_num⟩
  | 6 => ⟨((-257195622907967/4503599627370496), (-1124099341744069/9007199254740992)), (163737639/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-982282889/16777216)), (3/33554432), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-2045884431/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-324451719606335/9007199254740992), (272860417968789/2251799813685248)), (98307195/4503599627370496), by norm_num⟩
  | 1 => ⟨((370979903/4294967296), (-311990121/1073741824)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((-222392739/2147483648), (1496239273/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((88879083/1073741824), (-1195941693/4294967296)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((-213122733/4294967296), (716935733/4294967296)), (67/2147483648), by norm_num⟩
  | 5 => ⟨((408836795/17179869184), (-343827361/4294967296)), (259/17179869184), by norm_num⟩
  | 6 => ⟨((-163391303/17179869184), (1099282671/34359738368)), (209/34359738368), by norm_num⟩
  | 7 => ⟨((447765981/137438953472), (-753132777/68719476736)), (289/137438953472), by norm_num⟩
  | 8 => ⟨((-134211991/137438953472), (902966763/274877906944)), (175/274877906944), by norm_num⟩
  | 9 => ⟨((286067821/1099511627776), (-962319881/1099511627776)), (47/274877906944), by norm_num⟩
  | 10 => ⟨((-137192135/2199023255552), (923016917/4398046511104)), (91/2199023255552), by norm_num⟩
  | 11 => ⟨((119626317/8796093022208), (-1609671201/35184372088832)), (5/549755813888), by norm_num⟩
  | 12 => ⟨((-382468507/140737488355328), (1286607655/140737488355328)), (129/70368744177664), by norm_num⟩
  | 13 => ⟨((1102307/2199023255552), (-474638525/281474976710656)), (193/562949953421312), by norm_num⟩
  | 14 => ⟨((-386664849/4503599627370496), (325180993/1125899906842624)), (267/4503599627370496), by norm_num⟩
  | 15 => ⟨((61812121/4503599627370496), (-831733297/18014398509481984)), (43/4503599627370496), by norm_num⟩
  | 16 => ⟨((-296437985/144115188075855872), (997204671/144115188075855872)), (209/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (2422526404431/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778774605266037/633825300114114700748351602688), (2866964495923/633825300114114700748351602688)), (92483/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944874107780951/19807040628566084398385987584), (25193321195/309485009821345068724781056)), (104061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889523431088299/2475880078570760549798248448), (3425568098499/2475880078570760549798248448)), (55293/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771189393229471/154742504910672534362390528), (107023570309/4835703278458516698824704)), (55305/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549551906962733/9671406556917033397649408), (3209842595751/9671406556917033397649408)), (51861/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314696762521847/151115727451828646838272), (350968497919/75557863725914323419136)), (90781/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887788819204031/75557863725914323419136), (4560970412403/75557863725914323419136)), (73783/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297536534200459/4722366482869645213696), (1709655367795/2361183241434822606848)), (27679/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405360822269951/147573952589676412928), (4699250415143/590295810358705651712)), (152301/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823467369510255/73786976294838206464), (5870611821585/73786976294838206464)), (190477/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822647054000079/9223372036854775808), (6599695457101/9223372036854775808)), (214425/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796946726276245/576460752303423488), (1648442683691/288230376151711744)), (214599/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194497539798285/144115188075855872), (360180584105/9007199254740992)), (2937/2251799813685248), by norm_num⟩
  | 4 => ⟨((745753924197201/18014398509481984), (4315513541657/18014398509481984)), (141171/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489087511773331/9007199254740992), (2691381578575/2251799813685248)), (88403/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113791590002967/2251799813685248), (2682674792249/562949953421312)), (177319/1125899906842624), by norm_num⟩
  | 1 => ⟨((553873847687801/562949953421312), (8004593917211/562949953421312)), (267265/562949953421312), by norm_num⟩
  | 0 => ⟨((272409352397797/281474976710656), (63344345201761/2251799813685248)), (1079387/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272409352397797/281474976710656), (63344345201761/2251799813685248)), (4117534641746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2107303767685903/2251799813685248), (15326044481933/281474976710656)), (2149973/1125899906842624), by norm_num⟩
  | 2 => ⟨((491350999929099/562949953421312), (229481367458811/2251799813685248)), (8516301/2251799813685248), by norm_num⟩
  | 3 => ⟨((1692047028752005/2251799813685248), (400589426042983/2251799813685248)), (16602103/2251799813685248), by norm_num⟩
  | 4 => ⟨((1200173853300087/2251799813685248), (301010837626903/1125899906842624)), (30857243/2251799813685248), by norm_num⟩
  | 5 => ⟨((478722475292139/2251799813685248), (1283472304009219/4503599627370496)), (98784601/4503599627370496), by norm_num⟩
  | 6 => ⟨((-324451719606335/9007199254740992), (272860417968789/2251799813685248)), (98307195/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-2045884431/33554432)), (1/16777216), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-132507659/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((495644702533497/4503599627370496), (-364910300837119/9007199254740992)), (44607255/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1174574677/4294967296), (108095173/1073741824)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((364838553/1073741824), (-134303207/1073741824)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((-151098291/536870912), (27810911/268435456)), (29/1073741824), by norm_num⟩
  | 4 => ⟨((93866287/536870912), (-552860141/8589934592)), (147/8589934592), by norm_num⟩
  | 5 => ⟨((-1492793349/17179869184), (17172573/536870912)), (149/17179869184), by norm_num⟩
  | 6 => ⟨((154560505/4294967296), (-455170569/34359738368)), (63/17179869184), by norm_num⟩
  | 7 => ⟨((-877870689/68719476736), (80789741/17179869184)), (91/68719476736), by norm_num⟩
  | 8 => ⟨((272678339/68719476736), (-401509929/274877906944)), (115/274877906944), by norm_num⟩
  | 9 => ⟨((-602293527/549755813888), (27714297/68719476736)), (129/1099511627776), by norm_num⟩
  | 10 => ⟨((149664319/549755813888), (-220375811/2199023255552)), (65/2199023255552), by norm_num⟩
  | 11 => ⟨((-270474081/4398046511104), (398264231/17592186044416)), (15/2199023255552), by norm_num⟩
  | 12 => ⟨((896137123/70368744177664), (-329883145/70368744177664)), (101/70368744177664), by norm_num⟩
  | 13 => ⟨((-685174491/281474976710656), (504448505/562949953421312)), (157/562949953421312), by norm_num⟩
  | 14 => ⟨((243227807/562949953421312), (-44768123/281474976710656)), (113/2251799813685248), by norm_num⟩
  | 15 => ⟨((-644691621/9007199254740992), (237321827/9007199254740992)), (19/2251799813685248), by norm_num⟩
  | 16 => ⟨((50062453/4503599627370496), (-294861293/72057594037927936)), (3/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-114865104893/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889331580851565/316912650057057350374175801344), (-67960743367/79228162514264337593543950336)), (46127/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889623104865989/39614081257132168796771975168), (-611532467661/39614081257132168796771975168)), (103789/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118086927646009/154742504910672534362390528), (-324805616719/1237940039285380274899124224)), (13785/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771057188212789/154742504910672534362390528), (-649451530463/154742504910672534362390528)), (110285/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549428372231267/9671406556917033397649408), (-304345590247/4835703278458516698824704)), (103397/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258679364390785/604462909807314587353088), (-266217607807/302231454903657293676544)), (90477/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235951824105473/9444732965739290427392), (-864889418339/75557863725914323419136)), (73517/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297406531374325/4722366482869645213696), (-40524319639/295147905179352825856)), (27571/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621265617871361/590295810358705651712), (-445541805367/295147905179352825856)), (37913/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455811725645231/18446744073709551616), (-1113177812817/73786976294838206464)), (11849/4611686018427387904), by norm_num⟩
  | 7 => ⟨((113900078495295/576460752303423488), (-1251395276591/9223372036854775808)), (213309/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593650433794985/1152921504606846976), (-625117061459/576460752303423488)), (106671/576460752303423488), by norm_num⟩
  | 5 => ⟨((149286002331699/18014398509481984), (-273162500449/36028797018963968)), (23339/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491199791076757/36028797018963968), (-1636368892187/36028797018963968)), (280143/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488713296584039/9007199254740992), (-2040908512295/9007199254740992)), (175155/4503599627370496), by norm_num⟩
  | 2 => ⟨((139179198398075/281474976710656), (-508523939819/562949953421312)), (350509/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214501939437931/2251799813685248), (-1517084076847/562949953421312)), (1052531/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177607128800007/2251799813685248), (-12001543385153/2251799813685248)), (527279/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177607128800007/2251799813685248), (-12001543385153/2251799813685248)), (2011409761668968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2105794991872127/2251799813685248), (-23212228967495/2251799813685248)), (1025433/562949953421312), by norm_num⟩
  | 2 => ⟨((246127215287611/281474976710656), (-10853583700663/562949953421312)), (7756123/2251799813685248), by norm_num⟩
  | 3 => ⟨((1720910519095673/2251799813685248), (-75924683987273/2251799813685248)), (13863285/2251799813685248), by norm_num⟩
  | 4 => ⟨((1312624878611311/2251799813685248), (-116049025795839/2251799813685248)), (1382785/140737488355328), by norm_num⟩
  | 5 => ⟨((1518355837114523/4503599627370496), (-270590373926581/4503599627370496)), (56148477/4503599627370496), by norm_num⟩
  | 6 => ⟨((495644702533497/4503599627370496), (-364910300837119/9007199254740992)), (44607255/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-132507659/2097152)), (1/16777216), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1094207495/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-718918477371531/9007199254740992), (-674587953901319/9007199254740992)), (179775949/4503599627370496), by norm_num⟩
  | 1 => ⟨((879282707/4294967296), (206265919/1073741824)), (221/2147483648), by norm_num⟩
  | 2 => ⟨((-70478613/268435456), (-132265409/536870912)), (143/1073741824), by norm_num⟩
  | 3 => ⟨((482064195/2147483648), (28271173/134217728)), (491/4294967296), by norm_num⟩
  | 4 => ⟨((-154558781/1073741824), (-72514127/536870912)), (317/4294967296), by norm_num⟩
  | 5 => ⟨((317148357/4294967296), (595184203/8589934592)), (327/8589934592), by norm_num⟩
  | 6 => ⟨((-542312983/17179869184), (-1017744893/34359738368)), (281/17179869184), by norm_num⟩
  | 7 => ⟨((794860193/68719476736), (745846889/68719476736)), (207/34359738368), by norm_num⟩
  | 8 => ⟨((-1019388071/274877906944), (-478264875/137438953472)), (267/137438953472), by norm_num⟩
  | 9 => ⟨((36314983/34359738368), (545211193/549755813888)), (153/274877906944), by norm_num⟩
  | 10 => ⟨((-596134991/2199023255552), (-69921955/274877906944)), (79/549755813888), by norm_num⟩
  | 11 => ⟨((278010193/4398046511104), (260867307/4398046511104)), (37/1099511627776), by norm_num⟩
  | 12 => ⟨((-118847011/8796093022208), (-892148575/70368744177664)), (127/17592186044416), by norm_num⟩
  | 13 => ⟨((46897933/17592186044416), (176024301/70368744177664)), (403/281474976710656), by norm_num⟩
  | 14 => ⟨((-274950453/562949953421312), (-1031984955/2251799813685248)), (593/2251799813685248), by norm_num⟩
  | 15 => ⟨((752249587/9007199254740992), (705863773/9007199254740992)), (51/1125899906842624), by norm_num⟩
  | 16 => ⟨((-120592631/9007199254740992), (-14144569/1125899906842624)), (263/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-1555315691403/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778549658661439/633825300114114700748351602688), (-57506784909/9903520314283042199192993792)), (46281/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889495039163611/39614081257132168796771975168), (-1034918779801/9903520314283042199192993792)), (26039/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889254279717877/2475880078570760549798248448), (-2198705312605/1237940039285380274899124224)), (221385/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770920071680479/154742504910672534362390528), (-4396292350977/154742504910672534362390528)), (110723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549299237360305/9671406556917033397649408), (-4120336160587/9671406556917033397649408)), (103835/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314641445930009/151115727451828646838272), (-3604106500651/604462909807314587353088)), (11361/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887428923377725/75557863725914323419136), (-5854446830891/75557863725914323419136)), (147753/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1266861637687/4611686018427387904), (-2194443880869/2361183241434822606848)), (27717/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405267815306745/147573952589676412928), (-3015778660257/295147905179352825856)), (305059/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911500808597525/36893488147419103232), (-7534703566431/73786976294838206464)), (381581/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822122098172791/9223372036854775808), (-8470022930401/9223372036854775808)), (429635/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796683634631959/576460752303423488), (-1057734930323/144115188075855872)), (105/281474976710656), by norm_num⟩
  | 5 => ⟨((1194035752824379/144115188075855872), (-7394989606929/144115188075855872)), (94205/36028797018963968), by norm_num⟩
  | 4 => ⟨((745406212733875/18014398509481984), (-11074190900897/36028797018963968)), (70779/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488213457889395/9007199254740992), (-13810761675783/9007199254740992)), (709547/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112910421344031/2251799813685248), (-13762869666607/2251799813685248)), (356093/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106408323151949/1125899906842624), (-10262415792013/562949953421312)), (1074893/1125899906842624), by norm_num⟩
  | 0 => ⟨((271722297565677/281474976710656), (-40573315325739/1125899906842624)), (544085/281474976710656), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271722297565677/281474976710656), (-40573315325739/1125899906842624)), (2075519562841319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((523884010836097/562949953421312), (-9791877939739/140737488355328)), (2179361/562949953421312), by norm_num⟩
  | 2 => ⟨((969607906257607/1125899906842624), (-291595841229535/2251799813685248)), (17438035/2251799813685248), by norm_num⟩
  | 3 => ⟨((1632263139266979/2251799813685248), (-502235822864341/2251799813685248)), (8637751/562949953421312), by norm_num⟩
  | 4 => ⟨((66947617839471/140737488355328), (-728111811626139/2251799813685248)), (65502345/2251799813685248), by norm_num⟩
  | 5 => ⟨((274110056684649/2251799813685248), (-173178276373959/562949953421312)), (209355465/4503599627370496), by norm_num⟩
  | 6 => ⟨((-718918477371531/9007199254740992), (-674587953901319/9007199254740992)), (179775949/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1094207495/16777216)), (1/8388608), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-562910979/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-393934950606909/9007199254740992), (418358690175347/4503599627370496)), (164329875/4503599627370496), by norm_num⟩
  | 1 => ⟨((495727977/4294967296), (-1052925651/4294967296)), (415/4294967296), by norm_num⟩
  | 2 => ⟨((-654127275/4294967296), (694682789/2147483648)), (275/2147483648), by norm_num⟩
  | 3 => ⟨((143856615/1073741824), (-1222205137/4294967296)), (243/2147483648), by norm_num⟩
  | 4 => ⟨((-189822927/2147483648), (201591839/1073741824)), (161/2147483648), by norm_num⟩
  | 5 => ⟨((400762869/8589934592), (-26600621/268435456)), (171/4294967296), by norm_num⟩
  | 6 => ⟨((-88136349/4294967296), (374403007/8589934592)), (303/17179869184), by norm_num⟩
  | 7 => ⟨((265825003/34359738368), (-17644125/1073741824)), (459/68719476736), by norm_num⟩
  | 8 => ⟨((-350763711/137438953472), (372510859/68719476736)), (305/137438953472), by norm_num⟩
  | 9 => ⟨((411415797/549755813888), (-436923339/274877906944)), (45/68719476736), by norm_num⟩
  | 10 => ⟨((-217149975/1099511627776), (57653287/137438953472)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((416779079/8796093022208), (-885238281/8796093022208)), (369/8796093022208), by norm_num⟩
  | 12 => ⟨((-91658657/8796093022208), (194682881/8796093022208)), (327/35184372088832), by norm_num⟩
  | 13 => ⟨((297713785/140737488355328), (-316171867/70368744177664)), (533/281474976710656), by norm_num⟩
  | 14 => ⟨((-448962141/1125899906842624), (476797533/562949953421312)), (101/281474976710656), by norm_num⟩
  | 15 => ⟨((631912975/9007199254740992), (-1342182425/9007199254740992)), (571/9007199254740992), by norm_num⟩
  | 16 => ⟨((-208456821/18014398509481984), (885524091/36028797018963968)), (379/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (1309659100085/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111153328896095/39614081257132168796771975168), (387349464799/79228162514264337593543950336)), (92505/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944693367051021/19807040628566084398385987584), (3485446118857/39614081257132168796771975168)), (13011/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889139387613247/2475880078570760549798248448), (3702425815815/2475880078570760549798248448)), (13827/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770805384210967/154742504910672534362390528), (1850728896315/77371252455336267181195264)), (221283/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549191935154137/9671406556917033397649408), (867272105495/2417851639229258349412352)), (207507/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258472111441863/604462909807314587353088), (758606102431/151115727451828646838272)), (181623/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887277112779653/75557863725914323419136), (1232253219307/18889465931478580854784)), (295239/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324288203683455/1180591620717411303424), (3695074353323/4722366482869645213696)), (221519/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405228943261575/147573952589676412928), (2538994903507/295147905179352825856)), (304733/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822808122100565/73786976294838206464), (1585845799919/18446744073709551616)), (381133/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821905604116611/9223372036854775808), (3565333202131/4611686018427387904)), (429075/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593152257670261/1152921504606846976), (7123621862451/1152921504606846976)), (429449/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193849282093021/144115188075855872), (3112625499619/72057594037927936)), (188095/72057594037927936), by norm_num⟩
  | 4 => ⟨((93158502488313/2251799813685248), (9322057678949/36028797018963968)), (565129/36028797018963968), by norm_num⟩
  | 3 => ⟨((743936883878319/4503599627370496), (45409876511/35184372088832)), (353945/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112579381501611/2251799813685248), (2895885304279/562949953421312)), (1420227/4503599627370496), by norm_num⟩
  | 1 => ⟨((276483314438517/281474976710656), (4318029519695/281474976710656)), (535371/562949953421312), by norm_num⟩
  | 0 => ⟨((1086024251058825/1125899906842624), (68266208996327/2251799813685248)), (4327713/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086024251058825/1125899906842624), (68266208996327/2251799813685248)), (16508914956099700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1046526070305375/1125899906842624), (131696890722319/2251799813685248)), (8611281/2251799813685248), by norm_num⟩
  | 2 => ⟨((1937793566626185/2251799813685248), (244825012741261/2251799813685248)), (17015669/2251799813685248), by norm_num⟩
  | 3 => ⟨((1640956091006483/2251799813685248), (6583904735835/35184372088832)), (32985807/2251799813685248), by norm_num⟩
  | 4 => ⟨((1116966207250015/2251799813685248), (614130532248673/2251799813685248)), (60420547/2251799813685248), by norm_num⟩
  | 5 => ⟨((773121298090769/4503599627370496), (4759824835403/17592186044416)), (92897969/2251799813685248), by norm_num⟩
  | 6 => ⟨((-393934950606909/9007199254740992), (418358690175347/4503599627370496)), (164329875/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-562910979/8388608)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-72203395/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1685750419449279/18014398509481984), (110540289292553/4503599627370496)), (272896961/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1088403883/4294967296), (-142740561/2147483648)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((1473726177/4294967296), (386548605/4294967296)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((-332577039/1073741824), (-348931009/4294967296)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((900635317/4294967296), (14764417/268435456)), (19/536870912), by norm_num⟩
  | 5 => ⟨((-243896565/2147483648), (-255889807/8589934592)), (167/8589934592), by norm_num⟩
  | 6 => ⟨((440322761/8589934592), (230987481/17179869184)), (19/2147483648), by norm_num⟩
  | 7 => ⟨((-170345163/8589934592), (-178721627/34359738368)), (237/68719476736), by norm_num⟩
  | 8 => ⟨((461303253/68719476736), (241993569/137438953472)), (81/68719476736), by norm_num⟩
  | 9 => ⟨((-1110428771/549755813888), (-36407263/68719476736)), (197/549755813888), by norm_num⟩
  | 10 => ⟨((601419371/1099511627776), (315496627/2199023255552)), (27/274877906944), by norm_num⟩
  | 11 => ⟨((-148061259/1099511627776), (-77670973/2199023255552)), (215/8796093022208), by norm_num⟩
  | 12 => ⟨((534609763/17592186044416), (35056149/4398046511104)), (49/8796093022208), by norm_num⟩
  | 13 => ⟨((-222730781/35184372088832), (-58420807/35184372088832)), (165/140737488355328), by norm_num⟩
  | 14 => ⟨((689332727/562949953421312), (361614807/1125899906842624)), (257/1125899906842624), by norm_num⟩
  | 15 => ⟨((-62224921/281474976710656), (-261138947/4503599627370496)), (187/4503599627370496), by norm_num⟩
  | 16 => ⟨((674032839/18014398509481984), (353588689/36028797018963968)), (255/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (334139440757/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444591655946607/158456325028528675187087900672), (197633137429/316912650057057350374175801344)), (92239/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944644784442159/19807040628566084398385987584), (111146121031/9903520314283042199192993792)), (207543/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472259136696051/618970019642690137449562112), (236129257773/1237940039285380274899124224)), (27565/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442675747462569/38685626227668133590597632), (472132009671/154742504910672534362390528)), (220527/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549096414493187/9671406556917033397649408), (55311174295/1208925819614629174706176)), (206751/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629194502277557/302231454903657293676544), (387043909139/604462909807314587353088)), (180915/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471785737873639/18889465931478580854784), (314347316795/37778931862957161709568)), (293999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324263242371201/1180591620717411303424), (117825208861/1180591620717411303424)), (220511/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620779744931575/590295810358705651712), (323840567789/295147905179352825856)), (303221/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822639973104057/73786976294838206464), (809065523861/73786976294838206464)), (379055/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821719025877591/9223372036854775808), (454731232675/4611686018427387904)), (426475/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592968910061111/1152921504606846976), (454271532235/576460752303423488)), (106631/288230376151711744), by norm_num⟩
  | 5 => ⟨((298423119755247/36028797018963968), (396971052899/72057594037927936)), (23329/9007199254740992), by norm_num⟩
  | 4 => ⟨((372577016620097/9007199254740992), (1188850129309/36028797018963968)), (560007/36028797018963968), by norm_num⟩
  | 3 => ⟨((743800704450991/4503599627370496), (370614843265/2251799813685248)), (175051/2251799813685248), by norm_num⟩
  | 2 => ⟨((69520365047639/140737488355328), (2954136875499/4503599627370496)), (1400999/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105599665407819/1125899906842624), (4404348366699/2251799813685248)), (2102993/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171083981764799/2251799813685248), (8701853309309/2251799813685248)), (2106031/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2171083981764799/2251799813685248), (8701853309309/2251799813685248)), (8033870701316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2093227783828001/2251799813685248), (16779870232415/2251799813685248)), (2038679/562949953421312), by norm_num⟩
  | 2 => ⟨((972848688484011/1125899906842624), (15598229632161/1125899906842624)), (15282455/2251799813685248), by norm_num⟩
  | 3 => ⟨((1680773326593159/2251799813685248), (842366023619/35184372088832)), (13416731/1125899906842624), by norm_num⟩
  | 4 => ⟨((1253260843364119/2251799813685248), (80480409890649/2251799813685248)), (41342573/2251799813685248), by norm_num⟩
  | 5 => ⟨((173659491801545/562949953421312), (22396073079155/562949953421312)), (97948843/4503599627370496), by norm_num⟩
  | 6 => ⟨((1685750419449279/18014398509481984), (110540289292553/4503599627370496)), (272896961/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-72203395/1048576)), (1/8388608), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile034Terms1

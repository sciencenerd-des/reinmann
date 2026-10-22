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
namespace Reinmann.XiBand97.Tile018Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27177/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27177/1280))
  have he : value ((69/80), (27177/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1565365957/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1205564713804953/9007199254740992), (-615952447315841/9007199254740992)), (241768409/9007199254740992), by norm_num⟩
  | 1 => ⟨((1263092241/4294967296), (322672333/2147483648)), (1/16777216), by norm_num⟩
  | 2 => ⟨((-693824329/2147483648), (-708983581/4294967296)), (71/1073741824), by norm_num⟩
  | 3 => ⟨((508162623/2147483648), (519265383/4294967296)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((-1116547405/8589934592), (-570471331/8589934592)), (233/8589934592), by norm_num⟩
  | 5 => ⟨((61332635/1073741824), (125345363/4294967296)), (207/17179869184), by norm_num⟩
  | 6 => ⟨((-359364195/17179869184), (-367215883/34359738368)), (77/17179869184), by norm_num⟩
  | 7 => ⟨((451202195/68719476736), (115265109/34359738368)), (49/34359738368), by norm_num⟩
  | 8 => ⟨((-123924069/68719476736), (-506526661/549755813888)), (109/274877906944), by norm_num⟩
  | 9 => ⟨((968138703/2199023255552), (247322851/1099511627776)), (215/2199023255552), by norm_num⟩
  | 10 => ⟨((-850887261/8796093022208), (-217369539/4398046511104)), (191/8796093022208), by norm_num⟩
  | 11 => ⟨((1359702111/70368744177664), (694705009/70368744177664)), (77/17592186044416), by norm_num⟩
  | 12 => ⟨((-497928483/140737488355328), (-63600955/35184372088832)), (57/70368744177664), by norm_num⟩
  | 13 => ⟨((1346536247/2251799813685248), (687978247/2251799813685248)), (311/2251799813685248), by norm_num⟩
  | 14 => ⟨((-845326439/9007199254740992), (-215948959/4503599627370496)), (197/9007199254740992), by norm_num⟩
  | 15 => ⟨((990598415/72057594037927936), (253060459/36028797018963968)), (233/72057594037927936), by norm_num⟩
  | 16 => ⟨((-136035449/72057594037927936), (-139007665/144115188075855872)), (129/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-3476988013475/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444759198906485/158456325028528675187087900672), (-2058026807289/316912650057057350374175801344)), (92605/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890042859894103/39614081257132168796771975168), (-2314884032175/19807040628566084398385987584)), (104207/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472459020757383/618970019642690137449562112), (-4918174998311/2475880078570760549798248448)), (55375/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442875396697849/38685626227668133590597632), (-2458551122387/77371252455336267181195264)), (1731/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1549844101641329/9671406556917033397649408), (-576080458563/1208925819614629174706176)), (12987/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157380279239725/75557863725914323419136), (-2015711826331/302231454903657293676544)), (90945/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944101290647255/37778931862957161709568), (-6548927039447/75557863725914323419136)), (147853/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297846058667077/4722366482869645213696), (-1227456551769/1180591620717411303424)), (110949/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810933795508085/295147905179352825856), (-6747974306551/590295810358705651712)), (152651/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823995807519713/73786976294838206464), (-8430413692975/73786976294838206464)), (95479/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823238883151765/9223372036854775808), (-9477954861531/9223372036854775808)), (107513/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594481956812617/1152921504606846976), (-2367532847511/288230376151711744)), (107637/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195008746871427/144115188075855872), (-4138783301731/72057594037927936)), (188645/144115188075855872), by norm_num⟩
  | 4 => ⟨((746133603278061/18014398509481984), (-3099690202121/9007199254740992)), (283527/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490023703349963/9007199254740992), (-15467687318069/9007199254740992)), (88847/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114708343636435/2251799813685248), (-15421576386167/2251799813685248)), (178431/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109074480001461/1125899906842624), (-23017209061781/1125899906842624)), (67373/140737488355328), by norm_num⟩
  | 0 => ⟨((546049543570773/562949953421312), (-22787266203397/562949953421312)), (1092783/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546049543570773/562949953421312), (-22787266203397/562949953421312)), (4168636326316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057468226878289/1125899906842624), (-44206332140073/562949953421312)), (1104211/562949953421312), by norm_num⟩
  | 2 => ⟨((986253080672127/1125899906842624), (-166077966188125/1125899906842624)), (4495229/1125899906842624), by norm_num⟩
  | 3 => ⟨((839429191296827/1125899906842624), (-72739550287437/281474976710656)), (9201515/1125899906842624), by norm_num⟩
  | 4 => ⟨((550657024320731/1125899906842624), (-867710552271861/2251799813685248)), (36952759/2251799813685248), by norm_num⟩
  | 5 => ⟨((408536343608921/4503599627370496), (-848762679136643/2251799813685248)), (129249309/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1205564713804953/9007199254740992), (-615952447315841/9007199254740992)), (241768409/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1565365957/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1640427817/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((238167234314983/9007199254740992), (606521650969737/4503599627370496)), (93102801/4503599627370496), by norm_num⟩
  | 1 => ⟨((-65374413/1073741824), (-665935379/2147483648)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((150530149/2147483648), (1533372877/4294967296)), (241/4294967296), by norm_num⟩
  | 3 => ⟨((-115536159/2147483648), (-147113397/536870912)), (187/4294967296), by norm_num⟩
  | 4 => ⟨((266031837/8589934592), (338741115/2147483648)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-245024377/17179869184), (-1247968387/17179869184)), (203/17179869184), by norm_num⟩
  | 6 => ⟨((188063159/34359738368), (957851135/34359738368)), (79/17179869184), by norm_num⟩
  | 7 => ⟨((-247446529/137438953472), (-1260304997/137438953472)), (105/68719476736), by norm_num⟩
  | 8 => ⟨((284883345/549755813888), (725489875/274877906944)), (245/549755813888), by norm_num⟩
  | 9 => ⟨((-291541397/2199023255552), (-1484890819/2199023255552)), (253/2199023255552), by norm_num⟩
  | 10 => ⟨((134259775/4398046511104), (683817493/4398046511104)), (235/8796093022208), by norm_num⟩
  | 11 => ⟨((-224832405/35184372088832), (-1145125793/35184372088832)), (199/35184372088832), by norm_num⟩
  | 12 => ⟨((674083/549755813888), (878916527/140737488355328)), (77/70368744177664), by norm_num⟩
  | 13 => ⟨((-244520719/1125899906842624), (-622701567/562949953421312)), (221/1125899906842624), by norm_num⟩
  | 14 => ⟨((321731293/9007199254740992), (409663813/2251799813685248)), (293/9007199254740992), by norm_num⟩
  | 15 => ⟨((-98775157/18014398509481984), (-251542877/9007199254740992)), (91/18014398509481984), by norm_num⟩
  | 16 => ⟨((56859551/72057594037927936), (579198879/144115188075855872)), (211/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (896798492871/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778903328198673/633825300114114700748351602688), (66341853041/19807040628566084398385987584)), (92409/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59059159851335/1237940039285380274899124224), (2387888885603/39614081257132168796771975168)), (51987/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889677501694451/2475880078570760549798248448), (2536617689323/2475880078570760549798248448)), (13811/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885671796370823/77371252455336267181195264), (2536039314515/154742504910672534362390528)), (110505/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549696605863583/9671406556917033397649408), (297115311395/1208925819614629174706176)), (51809/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629456899183143/302231454903657293676544), (2079192990201/604462909807314587353088)), (22671/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887995041296347/75557863725914323419136), (844384344725/18889465931478580854784)), (147395/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324422856160487/1180591620717411303424), (2532146082919/4722366482869645213696)), (55289/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621656626761843/590295810358705651712), (435008158925/73786976294838206464)), (152093/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823734585782963/73786976294838206464), (543453678805/9223372036854775808)), (190191/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911474209606959/4611686018427387904), (4887713388965/9223372036854775808)), (214067/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594195749411899/1152921504606846976), (4883504234259/1152921504606846976)), (214195/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194763094921205/144115188075855872), (4268335022535/144115188075855872)), (187565/144115188075855872), by norm_num⟩
  | 4 => ⟨((372977066251329/9007199254740992), (199782826663/1125899906842624)), (70409/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489591664102683/9007199254740992), (7974795045317/9007199254740992)), (352551/9007199254740992), by norm_num⟩
  | 2 => ⟨((278575289785333/562949953421312), (15900128407141/4503599627370496)), (353311/2251799813685248), by norm_num⟩
  | 1 => ⟨((554262742270183/562949953421312), (741464415195/70368744177664)), (16621/35184372088832), by norm_num⟩
  | 0 => ⟨((545623046469113/562949953421312), (46962331012305/2251799813685248)), (2142783/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545623046469113/562949953421312), (46962331012305/2251799813685248)), (8174068459517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1057169170177211/1125899906842624), (22758444121451/562949953421312)), (132595/70368744177664), by norm_num⟩
  | 2 => ⟨((1981587991042943/2251799813685248), (42738302650489/562949953421312)), (8311115/2251799813685248), by norm_num⟩
  | 3 => ⟨((1730822581271991/2251799813685248), (300878281541969/2251799813685248)), (15889529/2251799813685248), by norm_num⟩
  | 4 => ⟨((1290176440144015/2251799813685248), (462533943507949/2251799813685248)), (7168215/562949953421312), by norm_num⟩
  | 5 => ⟨((644203622804115/2251799813685248), (132505206069857/562949953421312)), (44635603/2251799813685248), by norm_num⟩
  | 6 => ⟨((238167234314983/9007199254740992), (606521650969737/4503599627370496)), (93102801/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1640427817/33554432)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1708329529/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((113590378225577/1125899906842624), (-686102254648403/9007199254740992)), (59383563/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1039038967/4294967296), (392246569/2147483648)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((622876657/2147483648), (-470283097/2147483648)), (21/536870912), by norm_num⟩
  | 3 => ⟨((-995728661/4294967296), (751793077/4294967296)), (17/536870912), by norm_num⟩
  | 4 => ⟨((1193826525/8589934592), (-901360533/8589934592)), (83/4294967296), by norm_num⟩
  | 5 => ⟨((-143133549/2147483648), (13508551/268435456)), (81/8589934592), by norm_num⟩
  | 6 => ⟨((915251361/34359738368), (-345515633/17179869184)), (33/8589934592), by norm_num⟩
  | 7 => ⟨((-313525273/34359738368), (473434459/68719476736)), (23/17179869184), by norm_num⟩
  | 8 => ⟨((375900385/137438953472), (-283811563/137438953472)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((-801217561/1099511627776), (302466847/549755813888)), (121/1099511627776), by norm_num⟩
  | 10 => ⟨((768494321/4398046511104), (-290113529/2199023255552)), (59/2199023255552), by norm_num⟩
  | 11 => ⟨((-335048891/8796093022208), (252967949/8796093022208)), (105/17592186044416), by norm_num⟩
  | 12 => ⟨((1071216203/140737488355328), (-202196883/35184372088832)), (85/70368744177664), by norm_num⟩
  | 13 => ⟨((-790358237/562949953421312), (149183677/140737488355328)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((1082969303/4503599627370496), (-817661335/4503599627370496)), (89/2251799813685248), by norm_num⟩
  | 15 => ⟨((-346246263/9007199254740992), (522844333/18014398509481984)), (29/4503599627370496), by norm_num⟩
  | 16 => ⟨((830262277/144115188075855872), (-626862977/144115188075855872)), (141/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-842405350567/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778778472937293/633825300114114700748351602688), (-996953522089/633825300114114700748351602688)), (46149/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889752784986777/39614081257132168796771975168), (-1121370008481/39614081257132168796771975168)), (51921/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889528570306975/2475880078570760549798248448), (-1191204301687/2475880078570760549798248448)), (110339/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771194851919887/154742504910672534362390528), (-1190921654275/154742504910672534362390528)), (27587/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96847335231771/604462909807314587353088), (-279047207475/2417851639229258349412352)), (25865/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258792163720769/604462909807314587353088), (-976365108573/604462909807314587353088)), (11317/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943898881966435/37778931862957161709568), (-1586030800581/75557863725914323419136)), (147137/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648771898961467/2361183241434822606848), (-594515565861/2361183241434822606848)), (110367/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621454177895071/590295810358705651712), (-408529692093/147573952589676412928)), (151779/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227935291329895/9223372036854775808), (-1020725311703/36893488147419103232)), (189759/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56958304341709/288230376151711744), (-35859157717/144115188075855872)), (106763/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593914450467565/1152921504606846976), (-1146465261749/576460752303423488)), (213587/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298629627361543/36028797018963968), (-501001024343/36028797018963968)), (186957/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491544481754695/36028797018963968), (-3001391933095/36028797018963968)), (280571/36028797018963968), by norm_num⟩
  | 3 => ⟨((186142791870091/1125899906842624), (-1871839272261/4503599627370496)), (350953/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113859897430323/2251799813685248), (-7463226886543/4503599627370496)), (21957/140737488355328), by norm_num⟩
  | 1 => ⟨((69242727956303/70368744177664), (-2783675778347/562949953421312)), (527871/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090041962885207/1125899906842624), (-22029983860063/2251799813685248)), (1059375/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1090041962885207/1125899906842624), (-22029983860063/2251799813685248)), (4041194920066451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263804567258367/281474976710656), (-42656734765161/2251799813685248)), (4144001/2251799813685248), by norm_num⟩
  | 2 => ⟨((1977139689385123/2251799813685248), (-79957668613263/2251799813685248)), (7924703/2251799813685248), by norm_num⟩
  | 3 => ⟨((1733141684644149/2251799813685248), (-70204944118573/1125899906842624)), (1809873/281474976710656), by norm_num⟩
  | 4 => ⟨((1325191140083067/2251799813685248), (-108069211464123/1125899906842624)), (12046863/1125899906842624), by norm_num⟩
  | 5 => ⟨((759133085232455/2251799813685248), (-508792515844971/4503599627370496)), (32983725/2251799813685248), by norm_num⟩
  | 6 => ⟨((113590378225577/1125899906842624), (-686102254648403/9007199254740992)), (59383563/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1708329529/33554432)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1770318935/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-842541458354547/9007199254740992), (-637132720246633/9007199254740992)), (191992211/9007199254740992), by norm_num⟩
  | 1 => ⟨((62395241/268435456), (188733975/1073741824)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((-620185397/2147483648), (-468986309/2147483648)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((513700939/2147483648), (388462399/2147483648)), (243/4294967296), by norm_num⟩
  | 4 => ⟨((-19945295/134217728), (-482646399/4294967296)), (153/4294967296), by norm_num⟩
  | 5 => ⟨((634396111/8589934592), (239866249/4294967296)), (77/4294967296), by norm_num⟩
  | 6 => ⟨((-525471705/17179869184), (-794726983/34359738368)), (129/17179869184), by norm_num⟩
  | 7 => ⟨((746141791/68719476736), (564234961/68719476736)), (185/68719476736), by norm_num⟩
  | 8 => ⟨((-927046349/274877906944), (-701035603/274877906944)), (29/34359738368), by norm_num⟩
  | 9 => ⟨((1023832727/1099511627776), (6048639/8589934592)), (259/1099511627776), by norm_num⟩
  | 10 => ⟨((-254412875/1099511627776), (-769551527/4398046511104)), (65/1099511627776), by norm_num⟩
  | 11 => ⟨((229888089/4398046511104), (173842155/4398046511104)), (237/17592186044416), by norm_num⟩
  | 12 => ⟨((-761667255/70368744177664), (-575975369/70368744177664)), (99/35184372088832), by norm_num⟩
  | 13 => ⟨((1164721247/562949953421312), (880766169/562949953421312)), (305/562949953421312), by norm_num⟩
  | 14 => ⟨((-206730255/562949953421312), (-625320489/2251799813685248)), (219/2251799813685248), by norm_num⟩
  | 15 => ⟨((547952411/9007199254740992), (828726955/18014398509481984)), (293/18014398509481984), by norm_num⟩
  | 16 => ⟨((-680805295/72057594037927936), (-32176705/4503599627370496)), (23/9007199254740992), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-812221732141/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778655406727895/633825300114114700748351602688), (-3844453387063/633825300114114700748351602688)), (92579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944806972263193/19807040628566084398385987584), (-2162091746507/19807040628566084398385987584)), (104175/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944690269920265/1237940039285380274899124224), (-4593438568193/2475880078570760549798248448)), (110715/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110690390337861/9671406556917033397649408), (-1148076629729/38685626227668133590597632)), (55373/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549417433466721/9671406556917033397649408), (-4304084777757/9671406556917033397649408)), (51929/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629334556796347/302231454903657293676544), (-3764871842427/604462909807314587353088)), (45455/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887596662531203/75557863725914323419136), (-3057831441033/37778931862957161709568)), (147791/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297391971039461/4722366482869645213696), (-1146193888661/1180591620717411303424)), (110899/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621243791439323/590295810358705651712), (-1575215876487/147573952589676412928)), (152575/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911608457044025/36893488147419103232), (-7871276774765/73786976294838206464)), (95427/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455590951140667/2305843009213693952), (-8848585573973/9223372036854775808)), (214897/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199201043509383/144115188075855872), (-4420169380495/576460752303423488)), (215129/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194245991706305/144115188075855872), (-3863012253955/72057594037927936)), (188499/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491126376005297/36028797018963968), (-11570507348221/36028797018963968)), (283271/36028797018963968), by norm_num⟩
  | 3 => ⟨((744301718884663/4503599627370496), (-7215370072815/4503599627370496)), (177503/4503599627370496), by norm_num⟩
  | 2 => ⟨((69581045278029/140737488355328), (-7191107013497/1125899906842624)), (11137/70368744177664), by norm_num⟩
  | 1 => ⟨((1106978623178407/1125899906842624), (-10726116680055/562949953421312)), (538029/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087993395561007/1125899906842624), (-21210742129213/562949953421312)), (1089919/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087993395561007/1125899906842624), (-21210742129213/562949953421312)), (4157711033347701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((4100643597105/4398046511104), (-10248312132935/140737488355328)), (2188581/1125899906842624), by norm_num⟩
  | 2 => ⟨((1945615699555179/2251799813685248), (-76442439474801/562949953421312)), (8799821/2251799813685248), by norm_num⟩
  | 3 => ⟨((1639544191749321/2251799813685248), (-264193307860817/1125899906842624)), (17596405/2251799813685248), by norm_num⟩
  | 4 => ⟨((1069772155759617/2251799813685248), (-192360173746239/562949953421312)), (8470511/562949953421312), by norm_num⟩
  | 5 => ⟨((245303103225523/2251799813685248), (-731082955066173/2251799813685248)), (110695971/4503599627370496), by norm_num⟩
  | 6 => ⟨((-842541458354547/9007199254740992), (-637132720246633/9007199254740992)), (191992211/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1770318935/33554432)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-913671831/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-488813868493347/9007199254740992), (856138824387459/9007199254740992)), (176752129/9007199254740992), by norm_num⟩
  | 1 => ⟨((149462559/1073741824), (-523555929/2147483648)), (109/2147483648), by norm_num⟩
  | 2 => ⟨((-766727789/4294967296), (335723611/1073741824)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((655539317/4294967296), (-1148152081/4294967296)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((-6568067/67108864), (368118993/2147483648)), (159/4294967296), by norm_num⟩
  | 5 => ⟨((107819259/2147483648), (-188841315/2147483648)), (165/8589934592), by norm_num⟩
  | 6 => ⟨((-737469171/34359738368), (322912273/8589934592)), (285/34359738368), by norm_num⟩
  | 7 => ⟨((540448879/68719476736), (-473287787/34359738368)), (211/68719476736), by norm_num⟩
  | 8 => ⟨((-693112003/274877906944), (1213959205/274877906944)), (273/274877906944), by norm_num⟩
  | 9 => ⟨((197533021/274877906944), (-691943085/549755813888)), (79/274877906944), by norm_num⟩
  | 10 => ⟨((-101332439/549755813888), (709919589/2199023255552)), (41/549755813888), by norm_num⟩
  | 11 => ⟨((756109307/17592186044416), (-1324296577/17592186044416)), (309/17592186044416), by norm_num⟩
  | 12 => ⟨((-323230347/35184372088832), (566125609/35184372088832)), (133/35184372088832), by norm_num⟩
  | 13 => ⟨((255098299/140737488355328), (-893589857/281474976710656)), (53/70368744177664), by norm_num⟩
  | 14 => ⟨((-373893839/1125899906842624), (163715195/281474976710656)), (313/2251799813685248), by norm_num⟩
  | 15 => ⟨((511476673/9007199254740992), (-223957965/2251799813685248)), (27/1125899906842624), by norm_num⟩
  | 16 => ⟨((-327977941/36028797018963968), (1148881677/72057594037927936)), (279/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (1360957473891/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889275679188373/316912650057057350374175801344), (3220513048157/633825300114114700748351602688)), (92517/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118093565409953/2475880078570760549798248448), (905592224563/9903520314283042199192993792)), (52051/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889256537380729/2475880078570760549798248448), (3847897406697/2475880078570760549798248448)), (13829/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770922469633557/154742504910672534362390528), (3846919385661/154742504910672534362390528)), (110659/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774650817199105/4835703278458516698824704), (3605448025015/9671406556917033397649408)), (103771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629284014985495/302231454903657293676544), (3153728401995/604462909807314587353088)), (22707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887432852373385/75557863725914323419136), (5122861834095/75557863725914323419136)), (2307/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297269507479115/4722366482869645213696), (3840443501919/4722366482869645213696)), (55391/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621076043772451/590295810358705651712), (5277843757417/590295810358705651712)), (152401/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455752047005119/18446744073709551616), (3296578777957/36893488147419103232)), (95307/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56941571998351/288230376151711744), (463225193321/576460752303423488)), (53649/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593376490101221/1152921504606846976), (7404483887975/1152921504606846976)), (214791/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597022480174553/72057594037927936), (6470920814499/144115188075855872)), (188161/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490828508713257/36028797018963968), (9690392339203/36028797018963968)), (35335/4503599627370496), by norm_num⟩
  | 3 => ⟨((744118761494227/4503599627370496), (12085046528031/9007199254740992)), (177059/4503599627370496), by norm_num⟩
  | 2 => ⟨((556470199146753/1125899906842624), (24086407914505/4503599627370496)), (710545/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106467964464883/1125899906842624), (8980227928481/562949953421312)), (267901/562949953421312), by norm_num⟩
  | 0 => ⟨((2174133112161775/2251799813685248), (1109532769101/35184372088832)), (1083221/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174133112161775/2251799813685248), (1109532769101/35184372088832)), (4132160191062545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096905918010129/2251799813685248), (137121783855663/2251799813685248)), (4320077/2251799813685248), by norm_num⟩
  | 2 => ⟨((972158363894003/1125899906842624), (15961203473083/140737488355328)), (8571963/2251799813685248), by norm_num⟩
  | 3 => ⟨((824928786120863/1125899906842624), (27563404810443/140737488355328)), (8373619/1125899906842624), by norm_num⟩
  | 4 => ⟨((561225785797605/1125899906842624), (20195264191291/70368744177664)), (1943797/140737488355328), by norm_num⟩
  | 5 => ⟨((748077569776459/4503599627370496), (322134582550789/1125899906842624)), (97713663/4503599627370496), by norm_num⟩
  | 6 => ⟨((-488813868493347/9007199254740992), (856138824387459/9007199254740992)), (176752129/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-913671831/16777216)), (1/16777216), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1880140311/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((402174043526335/4503599627370496), (228202144350847/4503599627370496)), (88520645/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1012192113/4294967296), (-574339429/4294967296)), (113/4294967296), by norm_num⟩
  | 2 => ⟨((1335616507/4294967296), (189464335/1073741824)), (151/4294967296), by norm_num⟩
  | 3 => ⟨((-293730711/1073741824), (-333338161/2147483648)), (135/4294967296), by norm_num⟩
  | 4 => ⟨((387586093/2147483648), (219924629/2147483648)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((-818289535/8589934592), (-464314963/8589934592)), (49/4294967296), by norm_num⟩
  | 6 => ⟨((719837665/17179869184), (408451269/17179869184)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-271384695/17179869184), (-307978947/34359738368)), (135/68719476736), by norm_num⟩
  | 8 => ⟨((89524971/17179869184), (406387049/137438953472)), (91/137438953472), by norm_num⟩
  | 9 => ⟨((-840040999/549755813888), (-476657209/549755813888)), (109/549755813888), by norm_num⟩
  | 10 => ⟨((443383271/1099511627776), (62896285/274877906944)), (117/2199023255552), by norm_num⟩
  | 11 => ⟨((-425495953/4398046511104), (-482870987/8796093022208)), (57/4398046511104), by norm_num⟩
  | 12 => ⟨((748605475/35184372088832), (424774739/35184372088832)), (51/17592186044416), by norm_num⟩
  | 13 => ⟨((-607880851/140737488355328), (-344924581/140737488355328)), (21/35184372088832), by norm_num⟩
  | 14 => ⟨((916704237/1125899906842624), (4063731/8796093022208)), (129/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1290258685/9007199254740992), (-366060171/4503599627370496)), (23/1125899906842624), by norm_num⟩
  | 16 => ⟨((212816665/9007199254740992), (483026889/36028797018963968)), (31/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (21009501001/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778458067014375/633825300114114700748351602688), (795372191047/633825300114114700748351602688)), (46139/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944696203807871/19807040628566084398385987584), (894616706787/39614081257132168796771975168)), (103819/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944572884218173/1237940039285380274899124224), (950309618805/2475880078570760549798248448)), (110313/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770812161472565/154742504910672534362390528), (237515377623/38685626227668133590597632)), (6895/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549198709758669/9671406556917033397649408), (890419141157/9671406556917033397649408)), (12929/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258478459811611/604462909807314587353088), (778853325035/604462909807314587353088)), (45255/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887288216785251/75557863725914323419136), (632571474825/37778931862957161709568)), (36773/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648580915726101/2361183241434822606848), (237106359257/1180591620717411303424)), (55165/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405232322219621/147573952589676412928), (1303383744805/590295810358705651712)), (75861/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822826691356183/73786976294838206464), (407044635049/18446744073709551616)), (189681/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227741099147923/1152921504606846976), (457564171313/2305843009213693952)), (106715/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593178314457851/1152921504606846976), (1828453187373/1152921504606846976)), (213479/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37308603133845/4503599627370496), (49933436351/4503599627370496)), (5839/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490581484919401/36028797018963968), (37386838821/562949953421312)), (140191/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487941762259601/9007199254740992), (2983877635011/9007199254740992)), (350669/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225328144541105/4503599627370496), (5946599696671/4503599627370496)), (701917/4503599627370496), by norm_num⟩
  | 1 => ⟨((553050867432759/562949953421312), (8867195094205/2251799813685248)), (263583/562949953421312), by norm_num⟩
  | 0 => ⟨((2173050357581483/2251799813685248), (8762337833657/1125899906842624)), (2114535/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173050357581483/2251799813685248), (8762337833657/1125899906842624)), (8066310891158293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096918524298171/2251799813685248), (33823612999623/2251799813685248)), (4114085/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952182087427299/2251799813685248), (31497187372765/1125899906842624)), (7785821/2251799813685248), by norm_num⟩
  | 3 => ⟨((845334160720063/1125899906842624), (109225064536839/2251799813685248)), (6967673/1125899906842624), by norm_num⟩
  | 4 => ⟨((632034260128055/1125899906842624), (2562718877659/35184372088832)), (11138707/1125899906842624), by norm_num⟩
  | 5 => ⟨((697650217163581/2251799813685248), (368283083334383/4503599627370496)), (56512993/4503599627370496), by norm_num⟩
  | 6 => ⟨((402174043526335/4503599627370496), (228202144350847/4503599627370496)), (88520645/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1880140311/33554432)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-120580801/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((7933822722739/140737488355328), (-88519974554201/1125899906842624)), (109057785/9007199254740992), by norm_num⟩
  | 1 => ⟨((-655675971/4294967296), (457223005/2147483648)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((443900861/2147483648), (-619091425/2147483648)), (195/4294967296), by norm_num⟩
  | 3 => ⟨((-801403877/4294967296), (1117687105/4294967296)), (89/2147483648), by norm_num⟩
  | 4 => ⟨((271280241/2147483648), (-756688197/4294967296)), (123/4294967296), by norm_num⟩
  | 5 => ⟨((-587712409/8589934592), (409829925/4294967296)), (135/8589934592), by norm_num⟩
  | 6 => ⟨((132629559/4294967296), (-184973335/4294967296)), (31/4294967296), by norm_num⟩
  | 7 => ⟨((-820954295/68719476736), (1144953319/68719476736)), (97/34359738368), by norm_num⟩
  | 8 => ⟨((555796361/137438953472), (-387573883/68719476736)), (133/137438953472), by norm_num⟩
  | 9 => ⟨((-668944199/549755813888), (932950695/549755813888)), (81/274877906944), by norm_num⟩
  | 10 => ⟨((724613789/2199023255552), (-1010590927/2199023255552)), (177/2199023255552), by norm_num⟩
  | 11 => ⟨((-178390047/2199023255552), (62198431/549755813888)), (177/8796093022208), by norm_num⟩
  | 12 => ⟨((644118937/35184372088832), (-898327859/35184372088832)), (81/17592186044416), by norm_num⟩
  | 13 => ⟨((-536709667/140737488355328), (748528289/140737488355328)), (137/140737488355328), by norm_num⟩
  | 14 => ⟨((830535269/1125899906842624), (-1158315533/1125899906842624)), (215/1125899906842624), by norm_num⟩
  | 15 => ⟨((-599768321/4503599627370496), (836473763/4503599627370496)), (157/4503599627370496), by norm_num⟩
  | 16 => ⟨((812101361/36028797018963968), (-1132606471/36028797018963968)), (215/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-154479763441/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778365562482053/633825300114114700748351602688), (-365479995405/158456325028528675187087900672)), (92345/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889288315847721/39614081257132168796771975168), (-822162923497/19807040628566084398385987584)), (103897/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889035137539777/2475880078570760549798248448), (-873340006835/1237940039285380274899124224)), (110401/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885350746531585/77371252455336267181195264), (-1746211978509/154742504910672534362390528)), (110413/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387273729576927/2417851639229258349412352), (-1636576610365/9671406556917033397649408)), (51763/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39324612578755/18889465931478580854784), (-1431507603473/604462909807314587353088)), (90597/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943570249605293/37778931862957161709568), (-1162634256001/37778931862957161709568)), (36811/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324262744550187/1180591620717411303424), (-871568429675/2361183241434822606848)), (110455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620776760098251/590295810358705651712), (-1197745165293/295147905179352825856)), (151909/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227829484044541/9223372036854775808), (-748094987771/18446744073709551616)), (189937/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821713905035445/9223372036854775808), (-420462875797/1152921504606846976)), (213751/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99560197256775/72057594037927936), (-3360300657027/1152921504606846976)), (213839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193686733800411/144115188075855872), (-2936439826065/144115188075855872)), (93605/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490298031960795/36028797018963968), (-4397024214017/36028797018963968)), (140507/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487586396278337/9007199254740992), (-1370735687895/2251799813685248)), (351617/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224614286664199/4503599627370496), (-10925971390553/4503599627370496)), (22009/140737488355328), by norm_num⟩
  | 1 => ⟨((1105562474905023/1125899906842624), (-8144757767119/1125899906842624)), (1059077/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170862872680365/2251799813685248), (-32183320907941/2251799813685248)), (2128793/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170862872680365/2251799813685248), (-32183320907941/2251799813685248)), (8120700844771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2092375093559699/2251799813685248), (-62053097308207/2251799813685248)), (2082703/1125899906842624), by norm_num⟩
  | 2 => ⟨((1942527447901651/2251799813685248), (-7207476575895/140737488355328)), (7970575/2251799813685248), by norm_num⟩
  | 3 => ⟨((417456543765541/562949953421312), (-198962213158669/2251799813685248)), (14568103/2251799813685248), by norm_num⟩
  | 4 => ⟨((1220682884842779/2251799813685248), (-73770392323845/562949953421312)), (12090197/1125899906842624), by norm_num⟩
  | 5 => ⟨((623054307174027/2251799813685248), (-79980693461805/562949953421312)), (16276661/1125899906842624), by norm_num⟩
  | 6 => ⟨((7933822722739/140737488355328), (-88519974554201/1125899906842624)), (109057785/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-120580801/2097152)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile018Terms1

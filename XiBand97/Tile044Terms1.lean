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
namespace Reinmann.XiBand97.Tile044Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨44,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36127/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36127/1280))
  have he : value ((69/80), (36127/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1040438163/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((926651548135165/9007199254740992), (986965351400295/9007199254740992)), (234616465/9007199254740992), by norm_num⟩
  | 1 => ⟨((-970869807/4294967296), (-1034061683/4294967296)), (249/4294967296), by norm_num⟩
  | 2 => ⟨((266652375/1073741824), (142004109/536870912)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((-12206149/67108864), (-832039783/4294967296)), (103/2147483648), by norm_num⟩
  | 4 => ⟨((858228819/8589934592), (457044565/4294967296)), (229/8589934592), by norm_num⟩
  | 5 => ⟨((-377144291/8589934592), (-803383641/17179869184)), (203/17179869184), by norm_num⟩
  | 6 => ⟨((552447137/34359738368), (73550595/4294967296)), (151/34359738368), by norm_num⟩
  | 7 => ⟨((-43351801/8589934592), (-738775657/137438953472)), (3/2147483648), by norm_num⟩
  | 8 => ⟨((762029141/549755813888), (50726751/34359738368)), (213/549755813888), by norm_num⟩
  | 9 => ⟨((-744155181/2199023255552), (-396295339/1099511627776)), (105/1099511627776), by norm_num⟩
  | 10 => ⟨((654030421/8796093022208), (696599887/8796093022208)), (187/8796093022208), by norm_num⟩
  | 11 => ⟨((-130641065/8796093022208), (-278288435/17592186044416)), (151/35184372088832), by norm_num⟩
  | 12 => ⟨((382730345/140737488355328), (815282919/281474976710656)), (7/8796093022208), by norm_num⟩
  | 13 => ⟨((-1035008641/2251799813685248), (-275593795/562949953421312)), (305/2251799813685248), by norm_num⟩
  | 14 => ⟨((649756121/9007199254740992), (692047383/9007199254740992)), (97/4503599627370496), by norm_num⟩
  | 15 => ⟨((-380709365/36028797018963968), (-810977877/72057594037927936)), (229/72057594037927936), by norm_num⟩
  | 16 => ⟨((418251987/288230376151711744), (445475131/288230376151711744)), (127/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (66506950935/633825300114114700748351602688)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779045010127651/633825300114114700748351602688), (1259693388551/633825300114114700748351602688)), (69243/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890052569007405/39614081257132168796771975168), (354229787839/9903520314283042199192993792)), (155809/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889847003039297/2475880078570760549798248448), (1505185534587/2475880078570760549798248448)), (20695/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442878296482589/38685626227668133590597632), (94053636791/9671406556917033397649408)), (20697/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774927848494123/4835703278458516698824704), (1410456841421/9671406556917033397649408)), (38811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259053100527491/604462909807314587353088), (1233802132239/604462909807314587353088)), (8491/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944110794903817/37778931862957161709568), (125267308343/4722366482869645213696)), (55199/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162232686941989/590295810358705651712), (375659459041/1180591620717411303424)), (20703/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621890733115073/590295810358705651712), (2065201419415/590295810358705651712)), (227777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824027606457609/73786976294838206464), (645028526815/18446744073709551616)), (71197/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911639299833849/4611686018427387904), (2900721531905/9223372036854775808)), (320477/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797263296851733/576460752303423488), (1449169893663/576460752303423488)), (320591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298763332140899/36028797018963968), (2533370329655/144115188075855872)), (280647/144115188075855872), by norm_num⟩
  | 4 => ⟨((373086275106425/9007199254740992), (3794707716171/36028797018963968)), (421227/36028797018963968), by norm_num⟩
  | 3 => ⟨((745070148117111/4503599627370496), (4734039945213/9007199254740992)), (65873/1125899906842624), by norm_num⟩
  | 2 => ⟨((2229707302948307/4503599627370496), (4720050679579/2251799813685248)), (263831/1125899906842624), by norm_num⟩
  | 1 => ⟨((554681899122477/562949953421312), (7045199922045/1125899906842624)), (1586387/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092960571313043/1125899906842624), (3487869107373/281474976710656)), (3186435/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092960571313043/1125899906842624), (3487869107373/281474976710656)), (12155284890181731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((8287593991285/8796093022208), (27086623875473/1125899906842624)), (6265395/2251799813685248), by norm_num⟩
  | 2 => ⟨((124854402336481/140737488355328), (102083022863811/2251799813685248)), (12107853/2251799813685248), by norm_num⟩
  | 3 => ⟨((441898321583673/562949953421312), (90562329606047/1125899906842624)), (22580611/2251799813685248), by norm_num⟩
  | 4 => ⟨((1372937267749909/2251799813685248), (284354523583513/2251799813685248)), (39082731/2251799813685248), by norm_num⟩
  | 5 => ⟨((801181008689057/2251799813685248), (86686418639087/562949953421312)), (57528641/2251799813685248), by norm_num⟩
  | 6 => ⟨((926651548135165/9007199254740992), (986965351400295/9007199254740992)), (234616465/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1040438163/16777216)), (3/33554432), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-33319209/16777216), (-272582219/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-683677231769271/9007199254740992), (-514971654008589/4503599627370496)), (444668361/9007199254740992), by norm_num⟩
  | 1 => ⟨((750648977/4294967296), (1130834631/4294967296)), (491/4294967296), by norm_num⟩
  | 2 => ⟨((-216054143/1073741824), (-650960741/2147483648)), (71/536870912), by norm_num⟩
  | 3 => ⟨((165827683/1073741824), (499630833/2147483648)), (219/2147483648), by norm_num⟩
  | 4 => ⟨((-381832351/4294967296), (-287610627/2147483648)), (507/8589934592), by norm_num⟩
  | 5 => ⟨((21980037/536870912), (264899177/4294967296)), (469/17179869184), by norm_num⟩
  | 6 => ⟨((-539849659/34359738368), (-1588419/67108864)), (181/17179869184), by norm_num⟩
  | 7 => ⟨((710314159/137438953472), (1070071197/137438953472)), (479/137438953472), by norm_num⟩
  | 8 => ⟨((-817779397/549755813888), (-1231964993/549755813888)), (277/274877906944), by norm_num⟩
  | 9 => ⟨((209222961/549755813888), (1260757435/2199023255552)), (569/2199023255552), by norm_num⟩
  | 10 => ⟨((-385402937/4398046511104), (-580600255/4398046511104)), (527/8796093022208), by norm_num⟩
  | 11 => ⟨((645398587/35184372088832), (972277449/35184372088832)), (443/35184372088832), by norm_num⟩
  | 12 => ⟨((-247680861/70368744177664), (-93281315/17592186044416)), (171/70368744177664), by norm_num⟩
  | 13 => ⟨((701915395/1125899906842624), (264354665/281474976710656)), (487/1125899906842624), by norm_num⟩
  | 14 => ⟨((-230888561/2251799813685248), (-695656127/4503599627370496)), (161/2251799813685248), by norm_num⟩
  | 15 => ⟨((567083263/36028797018963968), (854297295/36028797018963968)), (397/36028797018963968), by norm_num⟩
  | 16 => ⟨((-326439367/144115188075855872), (-245886527/72057594037927936)), (459/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806918929/10141204801825835211973625643008), (-2809488791713/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111181238905577/39614081257132168796771975168), (-3325370308375/633825300114114700748351602688)), (92527/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889888972607413/39614081257132168796771975168), (-3740379733933/39614081257132168796771975168)), (52057/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889672842444107/2475880078570760549798248448), (-496668384785/309485009821345068724781056)), (221291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771338643791481/154742504910672534362390528), (-3972440026927/154742504910672534362390528)), (110673/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549691658604603/9671406556917033397649408), (-930799740547/2417851639229258349412352)), (103785/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((9835227828967/4722366482869645213696), (-3256835730055/604462909807314587353088)), (90841/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887986931437135/75557863725914323419136), (-2645276092723/37778931862957161709568)), (147671/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297684838749387/4722366482869645213696), (-3966334425325/4722366482869645213696)), (221603/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621646753815701/590295810358705651712), (-5451143601915/590295810358705651712)), (152429/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455930255013657/18446744073709551616), (-1702520389171/18446744073709551616)), (190653/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822931476406475/9223372036854775808), (-478503319205/576460752303423488)), (214645/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797088354239165/576460752303423488), (-1912361431271/288230376151711744)), (429691/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597372039313365/72057594037927936), (-6685836412029/144115188075855872)), (23527/9007199254740992), by norm_num⟩
  | 4 => ⟨((93242190117435/2251799813685248), (-5006954597845/18014398509481984)), (35347/2251799813685248), by norm_num⟩
  | 3 => ⟨((1489541940063689/9007199254740992), (-12491433503453/9007199254740992)), (708525/9007199254740992), by norm_num⟩
  | 2 => ⟨((557119598717881/1125899906842624), (-12452557037053/2251799813685248)), (355453/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108402139952093/1125899906842624), (-18581830069453/1125899906842624)), (268081/281474976710656), by norm_num⟩
  | 0 => ⟨((1090878944716217/1125899906842624), (-36776753130909/1125899906842624)), (2168585/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090878944716217/1125899906842624), (-36776753130909/1125899906842624)), (8272495274070357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527873008617481/562949953421312), (-35632817270623/562949953421312)), (4343935/1125899906842624), by norm_num⟩
  | 2 => ⟨((985452486049459/1125899906842624), (-66825131945907/562949953421312)), (8696449/1125899906842624), by norm_num⟩
  | 3 => ⟨((846659817119917/1125899906842624), (-467913653826295/2251799813685248)), (2160987/140737488355328), by norm_num⟩
  | 4 => ⟨((1176120621455579/2251799813685248), (-703728077724867/2251799813685248)), (66370335/2251799813685248), by norm_num⟩
  | 5 => ⟨((394362990634321/2251799813685248), (-183779459230651/562949953421312)), (110814639/2251799813685248), by norm_num⟩
  | 6 => ⟨((-683677231769271/9007199254740992), (-514971654008589/4503599627370496)), (444668361/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33319209/16777216), (-272582219/4194304)), (1/8388608), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-283865129/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((152662427142361/9007199254740992), (1128365200101499/9007199254740992)), (21924853/562949953421312), by norm_num⟩
  | 1 => ⟨((-174555069/4294967296), (-322544763/1073741824)), (403/4294967296), by norm_num⟩
  | 2 => ⟨((209282387/4294967296), (1546857125/4294967296)), (485/4294967296), by norm_num⟩
  | 3 => ⟨((-83639541/2147483648), (-1236400463/4294967296)), (195/2147483648), by norm_num⟩
  | 4 => ⟨((50139715/2147483648), (1482379413/8589934592)), (235/4294967296), by norm_num⟩
  | 5 => ⟨((-192367657/17179869184), (-1421836235/17179869184)), (453/17179869184), by norm_num⟩
  | 6 => ⟨((153759165/34359738368), (568235731/17179869184)), (91/8589934592), by norm_num⟩
  | 7 => ⟨((-105342393/68719476736), (-778611299/68719476736)), (501/137438953472), by norm_num⟩
  | 8 => ⟨((126300013/274877906944), (1867028353/549755813888)), (603/549755813888), by norm_num⟩
  | 9 => ⟨((-134601869/1099511627776), (-497437607/549755813888)), (323/1099511627776), by norm_num⟩
  | 10 => ⟨((64552237/2199023255552), (954242629/4398046511104)), (311/4398046511104), by norm_num⟩
  | 11 => ⟨((-225148369/35184372088832), (-1664126465/35184372088832)), (545/35184372088832), by norm_num⟩
  | 12 => ⟨((179960737/140737488355328), (1330133661/140737488355328)), (219/70368744177664), by norm_num⟩
  | 13 => ⟨((-132777539/562949953421312), (-122673893/70368744177664)), (325/562949953421312), by norm_num⟩
  | 14 => ⟨((181935219/4503599627370496), (672363767/2251799813685248)), (447/4503599627370496), by norm_num⟩
  | 15 => ⟨((-116336427/18014398509481984), (-859870879/18014398509481984)), (287/18014398509481984), by norm_num⟩
  | 16 => ⟨((34870321/36028797018963968), (515470079/72057594037927936)), (173/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (935482063037/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778776380641247/633825300114114700748351602688), (2214212283833/633825300114114700748351602688)), (46209/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889750313062727/39614081257132168796771975168), (622633920905/9903520314283042199192993792)), (6499/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1889525790138503/2475880078570760549798248448), (2645635617035/2475880078570760549798248448)), (220999/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771191898926135/154742504910672534362390528), (2645007431929/154742504910672534362390528)), (221035/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774777205883131/4835703278458516698824704), (619756799567/2417851639229258349412352)), (207259/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157348674674007/75557863725914323419136), (2168481728981/604462909807314587353088)), (181391/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471948231272657/18889465931478580854784), (220158279903/4722366482869645213696)), (18427/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297539868456037/4722366482869645213696), (1320402871565/2361183241434822606848)), (55297/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621448287354431/590295810358705651712), (453666445763/73786976294838206464)), (304237/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455868559272247/18446744073709551616), (4534001351993/73786976294838206464)), (95113/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822655630905113/9223372036854775808), (5097092009163/9223372036854775808)), (214111/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593903091172151/1152921504606846976), (5092521005275/1152921504606846976)), (428489/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597253582715921/72057594037927936), (4450818153025/144115188075855872)), (375229/144115188075855872), by norm_num⟩
  | 4 => ⟨((372881166016861/9007199254740992), (6665963399837/36028797018963968)), (281723/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489112676994101/9007199254740992), (2078629669339/2251799813685248)), (705363/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227645889418349/4503599627370496), (8287667519531/2251799813685248)), (1413901/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107810100070517/1125899906842624), (1545569478209/140737488355328)), (1064403/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179646210547751/2251799813685248), (24462422387425/1125899906842624)), (2144773/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179646210547751/2251799813685248), (24462422387425/1125899906842624)), (8181659702781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054370804602673/1125899906842624), (94714327505531/2251799813685248)), (4245297/1125899906842624), by norm_num⟩
  | 2 => ⟨((1970788141818115/2251799813685248), (88697068977879/1125899906842624)), (4154155/562949953421312), by norm_num⟩
  | 3 => ⟨((427717552459165/562949953421312), (77628184660673/562949953421312)), (31703999/2251799813685248), by norm_num⟩
  | 4 => ⟨((628532495838197/1125899906842624), (117960528971079/562949953421312)), (56919735/2251799813685248), by norm_num⟩
  | 5 => ⟨((602885479750707/2251799813685248), (526810777647215/2251799813685248)), (43702347/1125899906842624), by norm_num⟩
  | 6 => ⟨((152662427142361/9007199254740992), (1128365200101499/9007199254740992)), (21924853/562949953421312), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-283865129/4194304)), (1/8388608), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1176662475/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((276641524463775/4503599627370496), (-112478614635775/1125899906842624)), (136678857/9007199254740992), by norm_num⟩
  | 1 => ⟨((-655582775/4294967296), (1066203527/4294967296)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((407265499/2147483648), (-1324708117/4294967296)), (103/2147483648), by norm_num⟩
  | 3 => ⟨((-674677831/4294967296), (1097258669/4294967296)), (173/4294967296), by norm_num⟩
  | 4 => ⟨((419127857/4294967296), (-681646341/4294967296)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-416597439/8589934592), (338765505/4294967296)), (55/4294967296), by norm_num⟩
  | 6 => ⟨((172534291/8589934592), (-1122400875/34359738368)), (185/34359738368), by norm_num⟩
  | 7 => ⟨((-489978979/68719476736), (796874685/68719476736)), (133/68719476736), by norm_num⟩
  | 8 => ⟨((608776011/274877906944), (-495039801/137438953472)), (21/34359738368), by norm_num⟩
  | 9 => ⟨((-336167013/549755813888), (546723419/549755813888)), (47/274877906944), by norm_num⟩
  | 10 => ⟨((668274917/4398046511104), (-1086845327/4398046511104)), (189/4398046511104), by norm_num⟩
  | 11 => ⟨((-603854831/17592186044416), (982076065/17592186044416)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((500174295/70368744177664), (-813455781/70368744177664)), (145/70368744177664), by norm_num⟩
  | 13 => ⟨((-764853189/562949953421312), (1243914879/562949953421312)), (225/562949953421312), by norm_num⟩
  | 14 => ⟨((135756341/562949953421312), (-883146387/2251799813685248)), (81/1125899906842624), by norm_num⟩
  | 15 => ⟨((-179915645/4503599627370496), (73151211/1125899906842624)), (217/18014398509481984), by norm_num⟩
  | 16 => ⟨((447073583/72057594037927936), (-363547861/36028797018963968)), (137/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1328026208205/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222332749720387/79228162514264337593543950336), (-196434000571/79228162514264337593543950336)), (92355/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889621729995579/39614081257132168796771975168), (-1767574696727/39614081257132168796771975168)), (103909/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889389296034405/2475880078570760549798248448), (-1877637503879/2475880078570760549798248448)), (6901/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771055545806041/154742504910672534362390528), (-1877175727527/154742504910672534362390528)), (27607/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549426730430407/9671406556917033397649408), (-219920219493/1208925819614629174706176)), (103541/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258677825845967/604462909807314587353088), (-769475607605/302231454903657293676544)), (22653/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887611901676721/75557863725914323419136), (-1249938363961/37778931862957161709568)), (147269/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648702173003207/2361183241434822606848), (-1874103779133/4722366482869645213696)), (110475/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202657792740941/73786976294838206464), (-40243550645/9223372036854775808)), (151939/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823242401581297/73786976294838206464), (-804381758501/18446744073709551616)), (189979/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822395634805683/9223372036854775808), (-1808514452963/4611686018427387904)), (213803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593644117083651/1152921504606846976), (-3613670482529/1152921504606846976)), (213897/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597140855370737/72057594037927936), (-3158187341753/144115188075855872)), (46817/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491188772000593/36028797018963968), (-2364871040719/18014398509481984)), (281115/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488696807439493/9007199254740992), (-1474751584207/2251799813685248)), (175885/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226826089335597/4503599627370496), (-5879293100499/2251799813685248)), (176167/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107210090795961/1125899906842624), (-4384904533895/562949953421312)), (1059835/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177363907557443/2251799813685248), (-34688016812959/2251799813685248)), (2131051/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177363907557443/2251799813685248), (-34688016812959/2251799813685248)), (8129314431197356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((263106776777955/281474976710656), (-67082726780827/2251799813685248)), (2093435/1125899906842624), by norm_num⟩
  | 2 => ⟨((982749697376365/1125899906842624), (-125410224575117/2251799813685248)), (2019189/562949953421312), by norm_num⟩
  | 3 => ⟨((213576942040015/281474976710656), (-54732600784523/562949953421312)), (14999351/2251799813685248), by norm_num⟩
  | 4 => ⟨((637586989768187/1125899906842624), (-166119512889727/1125899906842624)), (25678961/2251799813685248), by norm_num⟩
  | 5 => ⟨((336549878595827/1125899906842624), (-752575887227057/4503599627370496)), (36661071/2251799813685248), by norm_num⟩
  | 6 => ⟨((276641524463775/4503599627370496), (-112478614635775/1125899906842624)), (136678857/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1176662475/16777216)), (1/16777216), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-303641151/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-488305416367441/4503599627370496), (67349769932669/4503599627370496)), (331762589/9007199254740992), by norm_num⟩
  | 1 => ⟨((597228367/2147483648), (-164746045/4294967296)), (51/536870912), by norm_num⟩
  | 2 => ⟨((-382965129/1073741824), (211282631/4294967296)), (263/2147483648), by norm_num⟩
  | 3 => ⟨((654857441/2147483648), (-180643083/4294967296)), (113/1073741824), by norm_num⟩
  | 4 => ⟨((-1679676173/8589934592), (57917545/2147483648)), (291/4294967296), by norm_num⟩
  | 5 => ⟨((1723313729/17179869184), (-14855557/1073741824)), (75/2147483648), by norm_num⟩
  | 6 => ⟨((-368351037/8589934592), (203220007/34359738368)), (129/8589934592), by norm_num⟩
  | 7 => ⟨((1079773435/68719476736), (-148928293/68719476736)), (95/17179869184), by norm_num⟩
  | 8 => ⟨((-1384782089/274877906944), (190996765/274877906944)), (245/137438953472), by norm_num⟩
  | 9 => ⟨((1578620413/1099511627776), (-217732013/1099511627776)), (561/1099511627776), by norm_num⟩
  | 10 => ⟨((-809816283/2199023255552), (223388635/4398046511104)), (289/2199023255552), by norm_num⟩
  | 11 => ⟨((188830705/2199023255552), (-208356559/17592186044416)), (541/17592186044416), by norm_num⟩
  | 12 => ⟨((-1291576521/70368744177664), (178141341/70368744177664)), (465/70368744177664), by norm_num⟩
  | 13 => ⟨((509665903/140737488355328), (-35147963/70368744177664)), (369/281474976710656), by norm_num⟩
  | 14 => ⟨((-373504923/562949953421312), (206063417/2251799813685248)), (543/2251799813685248), by norm_num⟩
  | 15 => ⟨((1021889293/9007199254740992), (-70472297/4503599627370496)), (373/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1310547143/72057594037927936), (180757873/72057594037927936)), (15/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (489217283483/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889272714693867/316912650057057350374175801344), (4630653565791/633825300114114700748351602688)), (185311/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944745022156047/19807040628566084398385987584), (81382022733/618970019642690137449562112)), (104267/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118078041385255/154742504910672534362390528), (5532725231985/2475880078570760549798248448)), (55409/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885457052528193/77371252455336267181195264), (2765658208981/77371252455336267181195264)), (13857/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549293273016125/9671406556917033397649408), (5184112476585/9671406556917033397649408)), (3249/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((629280097284609/302231454903657293676544), (2267300987863/302231454903657293676544)), (182025/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943709573603127/37778931862957161709568), (460370178721/4722366482869645213696)), (295943/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297258378390651/4722366482869645213696), (5521987939411/4722366482869645213696)), (222091/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621059361265425/590295810358705651712), (3794373114223/295147905179352825856)), (305591/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822985267644959/73786976294838206464), (4739976786039/36893488147419103232)), (191157/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911050840286025/4611686018427387904), (10656728903537/9223372036854775808)), (430551/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398336081509285/288230376151711744), (2661614789879/288230376151711744)), (215555/576460752303423488), by norm_num⟩
  | 5 => ⟨((298503210698483/36028797018963968), (1163012948785/18014398509481984)), (377851/144115188075855872), by norm_num⟩
  | 4 => ⟨((745386203773865/18014398509481984), (6966536145205/18014398509481984)), (568039/36028797018963968), by norm_num⟩
  | 3 => ⟨((744076790064733/4503599627370496), (4343993715309/2251799813685248)), (178065/2251799813685248), by norm_num⟩
  | 2 => ⟨((69552239673391/140737488355328), (1082217916967/140737488355328)), (357791/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106259930579683/1125899906842624), (12911110400335/562949953421312)), (1081701/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086447906094095/1125899906842624), (25520840357467/562949953421312)), (2196841/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086447906094095/1125899906842624), (25520840357467/562949953421312)), (8380283360007857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046064390207525/1125899906842624), (98506318011473/1125899906842624)), (4438911/1125899906842624), by norm_num⟩
  | 2 => ⟨((963271430418245/1125899906842624), (45760706993585/281474976710656)), (2256261/281474976710656), by norm_num⟩
  | 3 => ⟨((1588750769675983/2251799813685248), (313207107770529/1125899906842624)), (36754731/2251799813685248), by norm_num⟩
  | 4 => ⟨((473340086840437/1125899906842624), (883929433716475/2251799813685248)), (72313529/2251799813685248), by norm_num⟩
  | 5 => ⟨((6376682928917/281474976710656), (743226342543179/2251799813685248)), (235150289/4503599627370496), by norm_num⟩
  | 6 => ⟨((-488305416367441/4503599627370496), (67349769932669/4503599627370496)), (331762589/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-303641151/4194304)), (1/8388608), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1249656493/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((141371600484009/2251799813685248), (365891325777219/4503599627370496)), (113441043/4503599627370496), by norm_num⟩
  | 1 => ⟨((-355804213/2147483648), (-460437863/2147483648)), (9/134217728), by norm_num⟩
  | 2 => ⟨((234746929/1073741824), (303780479/1073741824)), (3/33554432), by norm_num⟩
  | 3 => ⟨((-413007069/2147483648), (-534462733/2147483648)), (85/1073741824), by norm_num⟩
  | 4 => ⟨((272487333/2147483648), (44077431/268435456)), (113/2147483648), by norm_num⟩
  | 5 => ⟨((-575287755/8589934592), (-744466351/8589934592)), (241/8589934592), by norm_num⟩
  | 6 => ⟨((506072455/17179869184), (163724115/4294967296)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((-763173841/68719476736), (-246901329/17179869184)), (325/68719476736), by norm_num⟩
  | 8 => ⟨((1966855/536870912), (325793381/68719476736)), (27/17179869184), by norm_num⟩
  | 9 => ⟨((-590579837/549755813888), (-764255475/549755813888)), (1/2147483648), by norm_num⟩
  | 10 => ⟨((623429619/2199023255552), (806765605/2199023255552)), (17/137438953472), by norm_num⟩
  | 11 => ⟨((-598278729/8796093022208), (-387109215/4398046511104)), (263/8796093022208), by norm_num⟩
  | 12 => ⟨((65787161/4398046511104), (681068941/35184372088832)), (233/35184372088832), by norm_num⟩
  | 13 => ⟨((-854725363/281474976710656), (-276519997/70368744177664)), (381/281474976710656), by norm_num⟩
  | 14 => ⟨((161119231/281474976710656), (208500607/281474976710656)), (289/1125899906842624), by norm_num⟩
  | 15 => ⟨((-907099493/9007199254740992), (-1173856117/9007199254740992)), (409/9007199254740992), by norm_num⟩
  | 16 => ⟨((598471891/36028797018963968), (774468397/36028797018963968)), (17/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (1189144184301/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222307168219205/79228162514264337593543950336), (703411083583/316912650057057350374175801344)), (184677/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944695777964179/19807040628566084398385987584), (1582361210219/39614081257132168796771975168)), (51945/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944572405284011/1237940039285380274899124224), (1680868465965/2475880078570760549798248448)), (110393/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((55337848252873/4835703278458516698824704), (1680429527609/154742504910672534362390528)), (220809/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774598846388293/4835703278458516698824704), (196867057973/1208925819614629174706176)), (103517/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258477506814173/604462909807314587353088), (43050105011/18889465931478580854784)), (181179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117955409367865/4722366482869645213696), (2237731992579/75557863725914323419136)), (147231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81072529868075/295147905179352825856), (419383769253/1180591620717411303424)), (220887/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810463629960211/295147905179352825856), (1152685026489/295147905179352825856)), (151893/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911411951895059/36893488147419103232), (719963188113/18446744073709551616)), (379831/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910962656049871/4611686018427387904), (3237279056255/9223372036854775808)), (213723/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796587201436551/576460752303423488), (404260983949/144115188075855872)), (427617/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193871394484009/144115188075855872), (22080006463/1125899906842624)), (374357/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490574662769137/36028797018963968), (2116099582265/18014398509481984)), (2195/140737488355328), by norm_num⟩
  | 3 => ⟨((1487931554980801/9007199254740992), (659717236281/1125899906842624)), (351537/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225302716934909/4503599627370496), (164344260923/70368744177664)), (1408177/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106076442701983/1125899906842624), (3920939009175/562949953421312)), (529339/562949953421312), by norm_num⟩
  | 0 => ⟨((2172899952835531/2251799813685248), (30996222505383/2251799813685248)), (4255177/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172899952835531/2251799813685248), (30996222505383/2251799813685248)), (16232212075240325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096337965095363/2251799813685248), (59820317961391/2251799813685248)), (4164655/1125899906842624), by norm_num⟩
  | 2 => ⟨((1950019875999927/2251799813685248), (111380774493721/2251799813685248)), (15951073/2251799813685248), by norm_num⟩
  | 3 => ⟨((420793604390729/562949953421312), (48226916697263/562949953421312)), (14602343/1125899906842624), by norm_num⟩
  | 4 => ⟨((620806240199615/1125899906842624), (72097272527901/562949953421312)), (24331821/1125899906842624), by norm_num⟩
  | 5 => ⟨((1295348969587921/4503599627370496), (636055641034165/4503599627370496)), (132259449/4503599627370496), by norm_num⟩
  | 6 => ⟨((141371600484009/2251799813685248), (365891325777219/4503599627370496)), (113441043/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1249656493/16777216)), (1/8388608), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1282326261/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((222665956822917/4503599627370496), (-374497906564383/4503599627370496)), (227863391/9007199254740992), by norm_num⟩
  | 1 => ⟨((-287528319/2147483648), (241794379/1073741824)), (37/536870912), by norm_num⟩
  | 2 => ⟨((389320561/2147483648), (-1309582633/4294967296)), (403/4294967296), by norm_num⟩
  | 3 => ⟨((-43929151/268435456), (147767313/536870912)), (183/2147483648), by norm_num⟩
  | 4 => ⟨((475849385/4294967296), (-800322603/4294967296)), (125/2147483648), by norm_num⟩
  | 5 => ⟨((-515449609/8589934592), (433462757/4294967296)), (273/8589934592), by norm_num⟩
  | 6 => ⟨((232643903/8589934592), (-782559271/17179869184)), (31/2147483648), by norm_num⟩
  | 7 => ⟨((-11250203/1073741824), (1210977023/68719476736)), (193/34359738368), by norm_num⟩
  | 8 => ⟨((60932229/17179869184), (-819846643/137438953472)), (263/137438953472), by norm_num⟩
  | 9 => ⟨((-293346729/274877906944), (493374637/274877906944)), (319/549755813888), by norm_num⟩
  | 10 => ⟨((635518135/2199023255552), (-267216657/549755813888)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((-625823641/8796093022208), (1052561631/8796093022208)), (345/8796093022208), by norm_num⟩
  | 12 => ⟨((141230153/8796093022208), (-118766239/4398046511104)), (313/35184372088832), by norm_num⟩
  | 13 => ⟨((-235358981/70368744177664), (395846077/70368744177664)), (263/140737488355328), by norm_num⟩
  | 14 => ⟨((728415927/1125899906842624), (-1225109769/1125899906842624)), (205/562949953421312), by norm_num⟩
  | 15 => ⟨((-526023173/4503599627370496), (442354501/2251799813685248)), (149/2251799813685248), by norm_num⟩
  | 16 => ⟨((178062145/9007199254740992), (-1197918195/36028797018963968)), (203/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1347392295801/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778365346442083/633825300114114700748351602688), (-796940840517/316912650057057350374175801344)), (92357/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944644030389293/19807040628566084398385987584), (-1792752379809/39614081257132168796771975168)), (12989/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889034850673057/2475880078570760549798248448), (-1904345610893/2475880078570760549798248448)), (55209/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770701188376229/154742504910672534362390528), (-951917648015/77371252455336267181195264)), (110431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48409206679477/302231454903657293676544), (-446075890385/2417851639229258349412352)), (103543/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629193658560545/302231454903657293676544), (-390180947895/151115727451828646838272)), (181229/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887140000022273/75557863725914323419136), (-2535160672603/75557863725914323419136)), (73637/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297050572853911/4722366482869645213696), (-1900482384353/4722366482869645213696)), (110479/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620776152504135/590295810358705651712), (-40808138967/9223372036854775808)), (303891/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822635037606373/73786976294838206464), (-815622239525/18446744073709551616)), (47497/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821712862635021/9223372036854775808), (-458416176369/1152921504606846976)), (427627/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199120248104043/144115188075855872), (-1831809763821/576460752303423488)), (106955/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193685564302663/144115188075855872), (-3201498207653/144115188075855872)), (11705/4503599627370496), by norm_num⟩
  | 4 => ⟨((745147994667417/18014398509481984), (-1198480347279/9007199254740992)), (140569/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487583340314375/9007199254740992), (-5977857965445/9007199254740992)), (87951/1125899906842624), by norm_num⟩
  | 2 => ⟨((2224606674598377/4503599627370496), (-11912190805291/4503599627370496)), (704757/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211109808937875/2251799813685248), (-8879922107945/1125899906842624)), (66251/70368744177664), by norm_num⟩
  | 0 => ⟨((2170817864457177/2251799813685248), (-4386017342599/281474976710656)), (4263229/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170817864457177/2251799813685248), (-4386017342599/281474976710656)), (16262928017623137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523050383357107/562949953421312), (-33826256644193/1125899906842624)), (4176341/1125899906842624), by norm_num⟩
  | 2 => ⟨((485470596381491/562949953421312), (-62857582269093/1125899906842624)), (8011625/1125899906842624), by norm_num⟩
  | 3 => ⟨((833800339133083/1125899906842624), (-108412862514041/1125899906842624)), (14712513/1125899906842624), by norm_num⟩
  | 4 => ⟨((592815429367/1099511627776), (-160573210782281/1125899906842624)), (24624435/1125899906842624), by norm_num⟩
  | 5 => ⟨((304394240861697/1125899906842624), (-692600419968481/4503599627370496)), (134307611/4503599627370496), by norm_num⟩
  | 6 => ⟨((222665956822917/4503599627370496), (-374497906564383/4503599627370496)), (227863391/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1282326261/16777216)), (1/8388608), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile044Terms1

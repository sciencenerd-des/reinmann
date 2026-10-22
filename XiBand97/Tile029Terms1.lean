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
namespace Reinmann.XiBand97.Tile029Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6223/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6223/256))
  have he : value ((69/80), (6223/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1792190519/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-676895262216613/4503599627370496), (5908678440559/9007199254740992)), (326219077/9007199254740992), by norm_num⟩
  | 1 => ⟨((1418391139/4294967296), (-6190631/4294967296)), (43/536870912), by norm_num⟩
  | 2 => ⟨((-97391371/268435456), (6801103/4294967296)), (95/1073741824), by norm_num⟩
  | 3 => ⟨((35665119/134217728), (-77831/67108864)), (35/536870912), by norm_num⟩
  | 4 => ⟨((-1253828417/8589934592), (2736195/4294967296)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((550988523/8589934592), (-1202407/4294967296)), (137/8589934592), by norm_num⟩
  | 6 => ⟨((-1614194033/68719476736), (3522611/34359738368)), (403/68719476736), by norm_num⟩
  | 7 => ⟨((2026712459/274877906944), (-8845677/274877906944)), (509/274877906944), by norm_num⟩
  | 8 => ⟨((-1113285607/549755813888), (4858985/549755813888)), (141/274877906944), by norm_num⟩
  | 9 => ⟨((543586333/1099511627776), (-2372507/1099511627776)), (277/2199023255552), by norm_num⟩
  | 10 => ⟨((-955505001/8796093022208), (8340689/17592186044416)), (489/17592186044416), by norm_num⟩
  | 11 => ⟨((1526879325/70368744177664), (-6664133/70368744177664)), (393/70368744177664), by norm_num⟩
  | 12 => ⟨((-1118298927/281474976710656), (2440433/140737488355328)), (145/140737488355328), by norm_num⟩
  | 13 => ⟨((378023675/562949953421312), (-6599605/2251799813685248)), (197/1125899906842624), by norm_num⟩
  | 14 => ⟨((-1898520937/18014398509481984), (2071545/4503599627370496)), (249/9007199254740992), by norm_num⟩
  | 15 => ⟨((1112393831/72057594037927936), (-4855093/72057594037927936)), (147/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1222089533/576460752303423488), (5333865/576460752303423488)), (325/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (2043294961027/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779033338949819/633825300114114700748351602688), (4837699513135/633825300114114700748351602688)), (69507/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890038774282913/39614081257132168796771975168), (1360367552163/9903520314283042199192993792)), (156437/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889831487901323/2475880078570760549798248448), (5780440096859/2475880078570760549798248448)), (166267/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771496705889871/154742504910672534362390528), (5779177705643/154742504910672534362390528)), (166327/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549839222339941/9671406556917033397649408), (2708318923441/4835703278458516698824704)), (155995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259037661272745/604462909807314587353088), (4738216906763/604462909807314587353088)), (136559/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888194582565323/75557863725914323419136), (7697087797907/75557863725914323419136)), (55507/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297839562886441/4722366482869645213696), (1442653899943/1180591620717411303424)), (166625/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101366115807591/36893488147419103232), (1982755305121/147573952589676412928)), (229279/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911991213349769/36893488147419103232), (1238551748847/9223372036854775808)), (286853/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823222170714285/9223372036854775808), (5569796380921/4611686018427387904)), (80765/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594463173999763/1152921504606846976), (11130377310697/1152921504606846976)), (161749/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194989987401935/144115188075855872), (608044615015/9007199254740992)), (141777/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492234429991087/36028797018963968), (14572340883893/36028797018963968)), (213159/18014398509481984), by norm_num⟩
  | 3 => ⟨((186246830434411/1125899906842624), (18179155107705/9007199254740992)), (133657/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114647202404153/2251799813685248), (18124761506821/2251799813685248)), (537227/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108952747999973/1125899906842624), (27051204832827/1125899906842624)), (406177/562949953421312), by norm_num⟩
  | 0 => ⟨((1091736640823869/1125899906842624), (53558950905625/1125899906842624)), (206357/140737488355328), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1091736640823869/1125899906842624), (53558950905625/1125899906842624)), (787189484179449037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((264015549799107/281474976710656), (103867615215871/1125899906842624)), (3358591/1125899906842624), by norm_num⟩
  | 2 => ⟨((980974312519723/1125899906842624), (194849757928781/1125899906842624)), (6920207/1125899906842624), by norm_num⟩
  | 3 => ⟨((205245636854787/281474976710656), (339537477829347/1125899906842624)), (14454121/1125899906842624), by norm_num⟩
  | 4 => ⟨((496248947993045/1125899906842624), (61895898071953/140737488355328)), (59594275/2251799813685248), by norm_num⟩
  | 5 => ⟨((3810206207979/4503599627370496), (872994812178019/2251799813685248)), (52476003/1125899906842624), by norm_num⟩
  | 6 => ⟨((-676895262216613/4503599627370496), (5908678440559/9007199254740992)), (326219077/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1792190519/33554432)), (3/33554432), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1878128989/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1036697325786023/9007199254740992), (673391668042945/9007199254740992)), (30706789/2251799813685248), by norm_num⟩
  | 1 => ⟨((-284562565/1073741824), (-369677929/2147483648)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((40951845/134217728), (106401861/536870912)), (81/2147483648), by norm_num⟩
  | 3 => ⟨((-251453621/1073741824), (-653331571/4294967296)), (127/4294967296), by norm_num⟩
  | 4 => ⟨((1157986719/8589934592), (94021971/1073741824)), (149/8589934592), by norm_num⟩
  | 5 => ⟨((-1066545183/17179869184), (-173194871/4294967296)), (35/4294967296), by norm_num⟩
  | 6 => ⟨((25581365/1073741824), (16616497/1073741824)), (109/34359738368), by norm_num⟩
  | 7 => ⟨((-1077088361/137438953472), (-699627855/137438953472)), (73/68719476736), by norm_num⟩
  | 8 => ⟨((620021901/274877906944), (805476335/549755813888)), (85/274877906944), by norm_num⟩
  | 9 => ⟨((-1269025055/2199023255552), (-824301245/2199023255552)), (177/2199023255552), by norm_num⟩
  | 10 => ⟨((584407635/4398046511104), (23725297/274877906944)), (83/4398046511104), by norm_num⟩
  | 11 => ⟨((-978653315/35184372088832), (-79461113/4398046511104)), (141/35184372088832), by norm_num⟩
  | 12 => ⟨((375572089/70368744177664), (487909265/140737488355328)), (55/70368744177664), by norm_num⟩
  | 13 => ⟨((-532176427/562949953421312), (-345677723/562949953421312)), (159/1125899906842624), by norm_num⟩
  | 14 => ⟨((175054501/1125899906842624), (454829927/4503599627370496)), (107/4503599627370496), by norm_num⟩
  | 15 => ⟨((-859899487/36028797018963968), (-34909487/2251799813685248)), (133/36028797018963968), by norm_num⟩
  | 16 => ⟨((494997935/144115188075855872), (643056515/288230376151711744)), (155/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (187596316609/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905317825461/633825300114114700748351602688), (444085929811/316912650057057350374175801344)), (721/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((944947733174143/19807040628566084398385987584), (999019656831/39614081257132168796771975168)), (103829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889680146005373/2475880078570760549798248448), (530621684851/1237940039285380274899124224)), (110325/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885673200733903/77371252455336267181195264), (265250390051/38685626227668133590597632)), (110333/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699413629191/9671406556917033397649408), (994432115945/9671406556917033397649408)), (103445/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258916429626331/604462909807314587353088), (869871340047/604462909807314587353088)), (45261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887999643961843/75557863725914323419136), (1413059681223/75557863725914323419136)), (147113/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297695162396451/4722366482869645213696), (1059373851559/4722366482869645213696)), (110347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810831115025383/295147905179352825856), (1455955407775/590295810358705651712)), (37937/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823742284876487/73786976294838206464), (1818919396491/73786976294838206464)), (47429/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911479017471787/4611686018427387904), (511219024665/2305843009213693952)), (106737/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594206555928573/1152921504606846976), (255389658301/144115188075855872)), (26691/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194773887478177/144115188075855872), (892875453977/72057594037927936)), (93449/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491927120609931/36028797018963968), (1337338960837/18014398509481984)), (280467/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489619884867429/9007199254740992), (417056097159/1125899906842624)), (350797/9007199254740992), by norm_num⟩
  | 2 => ⟨((557168162846825/1125899906842624), (1663061547563/1125899906842624)), (351117/2251799813685248), by norm_num⟩
  | 1 => ⟨((554297745156709/562949953421312), (9926896335221/2251799813685248)), (1054961/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091454479740763/1125899906842624), (19648831038149/2251799813685248)), (1058199/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091454479740763/1125899906842624), (19648831038149/2251799813685248)), (4036708836082076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528988569484085/562949953421312), (38095401781137/2251799813685248)), (4140235/2251799813685248), by norm_num⟩
  | 2 => ⟨((248457434997031/281474976710656), (8949300008665/281474976710656)), (3960509/1125899906842624), by norm_num⟩
  | 3 => ⟨((876113504015433/1125899906842624), (63196242910289/1125899906842624)), (14487423/2251799813685248), by norm_num⟩
  | 4 => ⟨((1356392521501391/2251799813685248), (49175847231403/562949953421312)), (6043245/562949953421312), by norm_num⟩
  | 5 => ⟨((799852828046213/2251799813685248), (473944449362093/4503599627370496)), (66689689/4503599627370496), by norm_num⟩
  | 6 => ⟨((1036697325786023/9007199254740992), (673391668042945/9007199254740992)), (30706789/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1878128989/33554432)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-977934895/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-192636426809047/9007199254740992), (-1122232172292087/9007199254740992)), (143724229/4503599627370496), by norm_num⟩
  | 1 => ⟨((220261563/4294967296), (641583257/2147483648)), (331/4294967296), by norm_num⟩
  | 2 => ⟨((-8252565/134217728), (-1538449459/4294967296)), (399/4294967296), by norm_num⟩
  | 3 => ⟨((105540195/2147483648), (307420057/1073741824)), (321/4294967296), by norm_num⟩
  | 4 => ⟨((-253074335/8589934592), (-1474322203/8589934592)), (387/8589934592), by norm_num⟩
  | 5 => ⟨((242738301/17179869184), (22095439/268435456)), (187/8589934592), by norm_num⟩
  | 6 => ⟨((-97010171/17179869184), (-1130294373/34359738368)), (301/34359738368), by norm_num⟩
  | 7 => ⟨((66462923/34359738368), (1548758591/137438953472)), (415/137438953472), by norm_num⟩
  | 8 => ⟨((-159371129/274877906944), (-464220113/137438953472)), (125/137438953472), by norm_num⟩
  | 9 => ⟨((84923395/549755813888), (494733873/549755813888)), (67/274877906944), by norm_num⟩
  | 10 => ⟨((-81454963/2199023255552), (-237264003/1099511627776)), (259/4398046511104), by norm_num⟩
  | 11 => ⟨((284102503/35184372088832), (206885175/4398046511104)), (227/17592186044416), by norm_num⟩
  | 12 => ⟨((-227082683/140737488355328), (-1322903955/140737488355328)), (365/140737488355328), by norm_num⟩
  | 13 => ⟨((167544767/562949953421312), (488028483/281474976710656)), (271/562949953421312), by norm_num⟩
  | 14 => ⟨((-114787087/2251799813685248), (-668709253/2251799813685248)), (187/2251799813685248), by norm_num⟩
  | 15 => ⟨((293597241/36028797018963968), (1710394407/36028797018963968)), (481/36028797018963968), by norm_num⟩
  | 16 => ⟨((-176003859/144115188075855872), (-512668333/72057594037927936)), (145/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-1133789445633/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444693787521273/158456325028528675187087900672), (-2683590222617/633825300114114700748351602688)), (17337/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944874429616699/19807040628566084398385987584), (-3018487715223/39614081257132168796771975168)), (156059/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944762077511187/1237940039285380274899124224), (-3206466002943/2475880078570760549798248448)), (82921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885595081082827/77371252455336267181195264), (-3205704345115/154742504910672534362390528)), (165875/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549552675624761/9671406556917033397649408), (-3004538758291/9671406556917033397649408)), (155543/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258787770416843/604462909807314587353088), (-2628162568871/604462909807314587353088)), (17017/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887790079198389/75557863725914323419136), (-2134624029735/37778931862957161709568)), (110643/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297537557400295/4722366482869645213696), (-3200609912683/4722366482869645213696)), (166023/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621444822925233/590295810358705651712), (-2199342272059/295147905179352825856)), (228375/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227933684624721/9223372036854775808), (-85861345133/1152921504606846976)), (142805/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822649686035985/9223372036854775808), (-6177578658169/9223372036854775808)), (321505/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796948205200221/576460752303423488), (-6172034663345/1152921504606846976)), (80437/288230376151711744), by norm_num⟩
  | 5 => ⟨((597250246829601/72057594037927936), (-674287310361/18014398509481984)), (281803/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491513008689851/36028797018963968), (-2019749222493/9007199254740992)), (105813/9007199254740992), by norm_num⟩
  | 3 => ⟨((744547617159183/4503599627370496), (-1259623259095/1125899906842624)), (66253/1125899906842624), by norm_num⟩
  | 2 => ⟨((2227602423833745/4503599627370496), (-5022201906757/1125899906842624)), (1062933/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107766845618499/1125899906842624), (-29970704381005/2251799813685248)), (800813/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089694393914599/1125899906842624), (-29646901506719/1125899906842624)), (6313/4398046511104), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089694393914599/1125899906842624), (-29646901506719/1125899906842624)), (24082183854667841/16777216000000000000000000), by norm_num⟩
  | 1 => ⟨((2107744971198067/2251799813685248), (-114774189685853/2251799813685248)), (803357/281474976710656), by norm_num⟩
  | 2 => ⟨((983527870033795/1125899906842624), (-214863434718717/2251799813685248)), (12686573/2251799813685248), by norm_num⟩
  | 3 => ⟨((1697816105019059/2251799813685248), (-46923393236985/281474976710656)), (3073217/281474976710656), by norm_num⟩
  | 4 => ⟨((1217543407054149/2251799813685248), (-566070161340061/2251799813685248)), (22635773/1125899906842624), by norm_num⟩
  | 5 => ⟨((129005308713455/562949953421312), (-76518235400077/281474976710656)), (71717695/2251799813685248), by norm_num⟩
  | 6 => ⟨((-192636426809047/9007199254740992), (-1122232172292087/9007199254740992)), (143724229/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-977934895/16777216)), (3/33554432), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1013420791/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-399043804417433/4503599627370496), (692004610446591/9007199254740992)), (288538221/9007199254740992), by norm_num⟩
  | 1 => ⟨((236412669/1073741824), (-409976687/2147483648)), (43/536870912), by norm_num⟩
  | 2 => ⟨((-587463413/2147483648), (254688449/1073741824)), (215/2147483648), by norm_num⟩
  | 3 => ⟨((486597247/2147483648), (-843836027/4294967296)), (179/2147483648), by norm_num⟩
  | 4 => ⟨((-604574367/4294967296), (524213439/4294967296)), (7/134217728), by norm_num⟩
  | 5 => ⟨((300462173/4294967296), (-65131073/1073741824)), (7/268435456), by norm_num⟩
  | 6 => ⟨((-995493935/34359738368), (431585697/17179869184)), (373/34359738368), by norm_num⟩
  | 7 => ⟨((353387071/34359738368), (-153207167/17179869184)), (267/68719476736), by norm_num⟩
  | 8 => ⟨((-439066941/137438953472), (95176377/34359738368)), (167/137438953472), by norm_num⟩
  | 9 => ⟨((484906827/549755813888), (-6569567/8589934592)), (371/1099511627776), by norm_num⟩
  | 10 => ⟨((-963958559/4398046511104), (835827749/4398046511104)), (371/4398046511104), by norm_num⟩
  | 11 => ⟨((871035285/17592186044416), (-755255975/17592186044416)), (337/17592186044416), by norm_num⟩
  | 12 => ⟨((-721480457/70368744177664), (312790099/35184372088832)), (281/70368744177664), by norm_num⟩
  | 13 => ⟨((275817167/140737488355328), (-478310275/281474976710656)), (27/35184372088832), by norm_num⟩
  | 14 => ⟨((-12238927/35184372088832), (169793769/562949953421312)), (309/2251799813685248), by norm_num⟩
  | 15 => ⟨((1038083109/18014398509481984), (-900099553/18014398509481984)), (103/4503599627370496), by norm_num⟩
  | 16 => ⟨((-644884905/72057594037927936), (559165841/72057594037927936)), (257/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (790446508477/2535301200456458802993406410752)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778655825339557/633825300114114700748351602688), (1870692839501/316912650057057350374175801344)), (34713/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236201804874909/4951760157141521099596496896), (4208255473537/39614081257132168796771975168)), (39061/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889381095964415/2475880078570760549798248448), (4470292144079/2475880078570760549798248448)), (166051/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885523418046553/77371252455336267181195264), (4469190590193/154742504910672534362390528)), (166097/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774709011967751/4835703278458516698824704), (4188695999055/9671406556917033397649408)), (155765/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629334833462513/302231454903657293676544), (457992383635/75557863725914323419136)), (17043/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887597630398613/75557863725914323419136), (371981743619/4722366482869645213696)), (221651/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324348189249177/1180591620717411303424), (2230931249971/2361183241434822606848)), (166319/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810622484807089/295147905179352825856), (6131944492695/590295810358705651712)), (228819/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823218532842341/73786976294838206464), (7660257687821/73786976294838206464)), (286221/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911182913076117/4611686018427387904), (8611367449647/9223372036854775808)), (161135/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593610619816511/1152921504606846976), (8603343630275/1152921504606846976)), (322609/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194248260266439/144115188075855872), (1879726178821/36028797018963968)), (35333/18014398509481984), by norm_num⟩
  | 4 => ⟨((186391292354205/4503599627370496), (5630164873835/18014398509481984)), (53095/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488609367723243/9007199254740992), (14043897231397/9007199254740992)), (8317/140737488355328), by norm_num⟩
  | 2 => ⟨((8697688374375/17592186044416), (6998345294619/1125899906842624)), (534299/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106993323345817/1125899906842624), (2609656222907/140737488355328)), (403245/562949953421312), by norm_num⟩
  | 0 => ⟨((1088037123144831/1125899906842624), (20642370078177/562949953421312)), (1633213/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088037123144831/1125899906842624), (20642370078177/562949953421312)), (6230213169578170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524966892877067/562949953421312), (79792758906019/1125899906842624)), (3276355/1125899906842624), by norm_num⟩
  | 2 => ⟨((1946876562353903/2251799813685248), (297636096867263/2251799813685248)), (13149963/2251799813685248), by norm_num⟩
  | 3 => ⟨((1643903281449509/2251799813685248), (257332262654839/1125899906842624)), (26214817/2251799813685248), by norm_num⟩
  | 4 => ⟨((541242256601621/1125899906842624), (751451080917883/2251799813685248)), (25129437/1125899906842624), by norm_num⟩
  | 5 => ⟨((539207784477651/4503599627370496), (180618666139819/562949953421312)), (163729545/4503599627370496), by norm_num⟩
  | 6 => ⟨((-399043804417433/4503599627370496), (692004610446591/9007199254740992)), (288538221/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1013420791/16777216)), (3/33554432), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1046064651/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((873746913348131/9007199254740992), (114148756035051/2251799813685248)), (91945169/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1068647663/4294967296), (-279222277/2147483648)), (227/4294967296), by norm_num⟩
  | 2 => ⟨((1370513569/4294967296), (89523875/536870912)), (147/2147483648), by norm_num⟩
  | 3 => ⟨((-585882983/2147483648), (-612331215/4294967296)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((751380091/4294967296), (392649639/4294967296)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((-770900753/8589934592), (-25178161/536870912)), (171/8589934592), by norm_num⟩
  | 6 => ⟨((1318214261/34359738368), (172215221/8589934592)), (295/34359738368), by norm_num⟩
  | 7 => ⟨((-60377729/4294967296), (-126206663/17179869184)), (109/34359738368), by norm_num⟩
  | 8 => ⟨((619463269/137438953472), (323713699/137438953472)), (141/137438953472), by norm_num⟩
  | 9 => ⟨((-88271773/68719476736), (-369026331/549755813888)), (81/274877906944), by norm_num⟩
  | 10 => ⟨((90565051/274877906944), (94653385/549755813888)), (21/274877906944), by norm_num⟩
  | 11 => ⟨((-337883301/4398046511104), (-706272405/17592186044416)), (79/4398046511104), by norm_num⟩
  | 12 => ⟨((1155538075/70368744177664), (75481373/8796093022208)), (17/4398046511104), by norm_num⟩
  | 13 => ⟨((-455984099/140737488355328), (-476568367/281474976710656)), (27/35184372088832), by norm_num⟩
  | 14 => ⟨((1336658425/2251799813685248), (698499273/2251799813685248)), (319/2251799813685248), by norm_num⟩
  | 15 => ⟨((-114282039/1125899906842624), (-238882035/4503599627370496)), (55/2251799813685248), by norm_num⟩
  | 16 => ⟨((586255285/36028797018963968), (306360161/36028797018963968)), (71/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (156815273773/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778556617766137/633825300114114700748351602688), (742162257123/633825300114114700748351602688)), (92273/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889503257996699/39614081257132168796771975168), (834771790273/39614081257132168796771975168)), (25953/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944631761620809/1237940039285380274899124224), (443372464513/1237940039285380274899124224)), (55153/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770929889596071/154742504910672534362390528), (443259954405/77371252455336267181195264)), (13789/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774654525766471/4835703278458516698824704), (830873410111/9671406556917033397649408)), (101/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((314643745132857/151115727451828646838272), (363387659501/302231454903657293676544)), (181005/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887445009849983/75557863725914323419136), (295140529565/18889465931478580854784)), (147079/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297279379802681/4722366482869645213696), (110628746949/590295810358705651712)), (6895/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1621090842417475/590295810358705651712), (1216280201429/590295810358705651712)), (303415/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227878565022139/9223372036854775808), (1519396852371/73786976294838206464)), (47415/9223372036854775808), by norm_num⟩
  | 7 => ⟨((56942365474705/288230376151711744), (427002886629/2305843009213693952)), (426807/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796702511172229/576460752303423488), (1706375672405/1152921504606846976)), (213449/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194073451504131/144115188075855872), (745620218953/72057594037927936)), (186819/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490878275906073/36028797018963968), (2233189306951/36028797018963968)), (560661/36028797018963968), by norm_num⟩
  | 3 => ⟨((744155994710213/4503599627370496), (2785073456203/9007199254740992)), (701185/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226066318763571/4503599627370496), (5550954032619/4503599627370496)), (701725/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213305046952651/2251799813685248), (8278611744193/2251799813685248)), (2107893/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175230872164659/2251799813685248), (16366920527951/2251799813685248)), (2113373/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175230872164659/2251799813685248), (16366920527951/2251799813685248)), (8061878208640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1050573288614721/1125899906842624), (3952597228925/281474976710656)), (257109/70368744177664), by norm_num⟩
  | 2 => ⟨((1960128533001687/2251799813685248), (59010475714575/2251799813685248)), (7792575/1125899906842624), by norm_num⟩
  | 3 => ⟨((852345223210823/1125899906842624), (51366962769591/1125899906842624)), (27949719/2251799813685248), by norm_num⟩
  | 4 => ⟨((642911337204075/1125899906842624), (77773139657305/1125899906842624)), (22434057/1125899906842624), by norm_num⟩
  | 5 => ⟨((1446971702468777/4503599627370496), (355280130404177/4503599627370496)), (28719919/1125899906842624), by norm_num⟩
  | 6 => ⟨((873746913348131/9007199254740992), (114148756035051/2251799813685248)), (91945169/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1046064651/16777216)), (1/8388608), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-67268009/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((459176572332717/18014398509481984), (-895862678509277/9007199254740992)), (273939889/18014398509481984), by norm_num⟩
  | 1 => ⟨((-72228509/1073741824), (563677065/2147483648)), (175/4294967296), by norm_num⟩
  | 2 => ⟨((23826897/268435456), (-743788045/2147483648)), (233/4294967296), by norm_num⟩
  | 3 => ⟨((-167681459/2147483648), (163574941/536870912)), (207/4294967296), by norm_num⟩
  | 4 => ⟨((55315123/1073741824), (-431683647/2147483648)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((-233567649/8589934592), (455695157/4294967296)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((410932277/34359738368), (-100217137/2147483648)), (261/34359738368), by norm_num⟩
  | 7 => ⟨((-77462417/17179869184), (1209045805/68719476736)), (199/68719476736), by norm_num⟩
  | 8 => ⟨((408855519/274877906944), (-398842649/68719476736)), (265/274877906944), by norm_num⟩
  | 9 => ⟨((-468313/1073741824), (935616547/549755813888)), (79/274877906944), by norm_num⟩
  | 10 => ⟨((126556657/1099511627776), (-493829141/1099511627776)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((-242902017/8796093022208), (59238337/549755813888)), (41/2199023255552), by norm_num⟩
  | 12 => ⟨((427354899/70368744177664), (-1667555919/70368744177664)), (291/70368744177664), by norm_num⟩
  | 13 => ⟨((-86754929/70368744177664), (1354084821/281474976710656)), (239/281474976710656), by norm_num⟩
  | 14 => ⟨((130829275/562949953421312), (-1021002135/1125899906842624)), (91/562949953421312), by norm_num⟩
  | 15 => ⟨((-368283687/9007199254740992), (1437057689/9007199254740992)), (259/9007199254740992), by norm_num⟩
  | 16 => ⟨((242980441/36028797018963968), (-948119407/36028797018963968)), (173/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-1719342423813/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444614047416715/158456325028528675187087900672), (-1017037743069/316912650057057350374175801344)), (5775/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944695095392345/19807040628566084398385987584), (-285984977937/4951760157141521099596496896)), (25991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889143275231799/2475880078570760549798248448), (-1215153894709/1237940039285380274899124224)), (27619/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885404756682773/77371252455336267181195264), (-303709115607/19342813113834066795298816)), (110493/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549196062689251/9671406556917033397649408), (-2277144032159/9671406556917033397649408)), (103605/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258475979286003/604462909807314587353088), (-497956732009/151115727451828646838272)), (90673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943641939034153/37778931862957161709568), (-202215957445/4722366482869645213696)), (9211/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((162144788538591/590295810358705651712), (-2425486478827/4722366482869645213696)), (110561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620924007773061/590295810358705651712), (-3333249200687/590295810358705651712)), (152069/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227852429462231/9223372036854775808), (-1040967768413/18446744073709551616)), (190157/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821919732395403/9223372036854775808), (-1170164568675/2305843009213693952)), (214025/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593168133138493/1152921504606846976), (-4676041399413/1152921504606846976)), (53537/288230376151711744), by norm_num⟩
  | 5 => ⟨((298466283507337/36028797018963968), (-4086347706031/144115188075855872)), (187519/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490563727823099/36028797018963968), (-3059579087255/18014398509481984)), (281555/36028797018963968), by norm_num⟩
  | 3 => ⟨((743957597092711/4503599627370496), (-7630842476665/9007199254740992)), (176215/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112630980144935/2251799813685248), (-15207491773073/4503599627370496)), (44145/281474976710656), by norm_num⟩
  | 1 => ⟨((2212071806789009/2251799813685248), (-11338091398369/1125899906842624)), (132893/281474976710656), by norm_num⟩
  | 0 => ⟨((2172658880905223/2251799813685248), (-44814708142781/2251799813685248)), (2141009/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172658880905223/2251799813685248), (-44814708142781/2251799813685248)), (8167301186568450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((130962969766291/140737488355328), (-21619833399453/562949953421312)), (527093/281474976710656), by norm_num⟩
  | 2 => ⟨((973277899177145/1125899906842624), (-10059144940459/140737488355328)), (8171649/2251799813685248), by norm_num⟩
  | 3 => ⟨((1671185749115541/2251799813685248), (-69564574226663/562949953421312)), (3824001/562949953421312), by norm_num⟩
  | 4 => ⟨((602947498207103/1125899906842624), (-206510941841901/1125899906842624)), (13242165/1125899906842624), by norm_num⟩
  | 5 => ⟨((71253873133731/281474976710656), (-884734104545023/4503599627370496)), (76162951/4503599627370496), by norm_num⟩
  | 6 => ⟨((459176572332717/18014398509481984), (-895862678509277/9007199254740992)), (273939889/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-67268009/1048576)), (1/16777216), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1104425543/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-862298672944653/9007199254740992), (-1961310350125/140737488355328)), (588831839/18014398509481984), by norm_num⟩
  | 1 => ⟨((1113485381/4294967296), (162088833/4294967296)), (191/2147483648), by norm_num⟩
  | 2 => ⟨((-1507687155/4294967296), (-54868087/1073741824)), (65/536870912), by norm_num⟩
  | 3 => ⟨((170120521/536870912), (198114045/4294967296)), (59/536870912), by norm_num⟩
  | 4 => ⟨((-460694911/2147483648), (-134125695/4294967296)), (321/4294967296), by norm_num⟩
  | 5 => ⟨((998067957/8589934592), (72643823/4294967296)), (349/8589934592), by norm_num⟩
  | 6 => ⟨((-900939377/17179869184), (-262297493/34359738368)), (633/34359738368), by norm_num⟩
  | 7 => ⟨((697082589/34359738368), (25368385/8589934592)), (123/17179869184), by norm_num⟩
  | 8 => ⟨((-943867323/137438953472), (-17174715/17179869184)), (335/137438953472), by norm_num⟩
  | 9 => ⟨((1136017819/549755813888), (165368855/549755813888)), (405/549755813888), by norm_num⟩
  | 10 => ⟨((-1230557313/2199023255552), (-11195679/137438953472)), (441/2199023255552), by norm_num⟩
  | 11 => ⟨((605892905/4398046511104), (176398317/8796093022208)), (109/2199023255552), by norm_num⟩
  | 12 => ⟨((-1093858935/35184372088832), (-159231833/35184372088832)), (99/8796093022208), by norm_num⟩
  | 13 => ⟨((455726909/70368744177664), (265358645/281474976710656)), (331/140737488355328), by norm_num⟩
  | 14 => ⟨((-705217913/562949953421312), (-205315581/1125899906842624)), (515/1125899906842624), by norm_num⟩
  | 15 => ⟨((509270803/2251799813685248), (148267973/4503599627370496)), (187/2251799813685248), by norm_num⟩
  | 16 => ⟨((-344782725/9007199254740992), (-200758557/36028797018963968)), (127/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-1951989024183/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778355281342021/633825300114114700748351602688), (-4618164371165/633825300114114700748351602688)), (185309/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889276177346247/39614081257132168796771975168), (-2597174656035/19807040628566084398385987584)), (208531/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889021485898593/2475880078570760549798248448), (-1379419474253/618970019642690137449562112)), (3463/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((885343496693991/77371252455336267181195264), (-5516194970609/154742504910672534362390528)), (55427/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774540212236715/4835703278458516698824704), (-5169857434259/9671406556917033397649408)), (207933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258374020754415/604462909807314587353088), (-4522050194513/604462909807314587353088)), (182023/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943558371761821/37778931862957161709568), (-7345378944853/75557863725914323419136)), (147969/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324257922082015/1180591620717411303424), (-172076602583/147573952589676412928)), (222087/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620747845619465/590295810358705651712), (-7567174417883/590295810358705651712)), (305585/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822596147966047/73786976294838206464), (-9452675908803/73786976294838206464)), (191153/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910832149521059/4611686018427387904), (-10625612043801/9223372036854775808)), (107635/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796453708683997/576460752303423488), (-10614806561903/1152921504606846976)), (215549/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193631079983301/144115188075855872), (-9275806404901/144115188075855872)), (23615/9007199254740992), by norm_num⟩
  | 4 => ⟨((1490200828640203/36028797018963968), (-6944714020161/18014398509481984)), (568019/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487440972471123/9007199254740992), (-17319330881485/9007199254740992)), (356115/4503599627370496), by norm_num⟩
  | 2 => ⟨((139015753675135/281474976710656), (-8627863491655/1125899906842624)), (357773/1125899906842624), by norm_num⟩
  | 1 => ⟨((552601119812589/562949953421312), (-25724852405359/1125899906842624)), (540815/562949953421312), by norm_num⟩
  | 0 => ⟨((1084360659116473/1125899906842624), (-50816389995423/1125899906842624)), (2196643/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084360659116473/1125899906842624), (-50816389995423/1125899906842624)), (8379528049949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((65128776457887/70368744177664), (-97883113435693/1125899906842624)), (4429487/1125899906842624), by norm_num⟩
  | 2 => ⟨((955954268603863/1125899906842624), (-181188608336107/1125899906842624)), (8969475/1125899906842624), by norm_num⟩
  | 3 => ⟨((1565004573704647/2251799813685248), (-153839628646053/562949953421312)), (36236169/2251799813685248), by norm_num⟩
  | 4 => ⟨((919519222650845/2251799813685248), (-3341212340803/8796093022208)), (70173207/2251799813685248), by norm_num⟩
  | 5 => ⟨((50577925742209/2251799813685248), (-349281091794931/1125899906842624)), (221242213/4503599627370496), by norm_num⟩
  | 6 => ⟨((-862298672944653/9007199254740992), (-1961310350125/140737488355328)), (588831839/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1104425543/16777216)), (1/8388608), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile029Terms1

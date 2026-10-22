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
namespace Reinmann.XiBand97.Tile040Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6939/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6939/256))
  have he : value ((69/80), (6939/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1998394667/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-1341764927783667/9007199254740992), (-90070215798147/4503599627370496)), (339642939/9007199254740992), by norm_num⟩
  | 1 => ⟨((1405791701/4294967296), (188736431/4294967296)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((-772210019/2147483648), (-103674081/2147483648)), (99/1073741824), by norm_num⟩
  | 3 => ⟨((1131145889/4294967296), (151863493/4294967296)), (73/1073741824), by norm_num⟩
  | 4 => ⟨((-621345387/4294967296), (-41709775/2147483648)), (323/8589934592), by norm_num⟩
  | 5 => ⟨((1092188285/17179869184), (36658297/4294967296)), (143/8589934592), by norm_num⟩
  | 6 => ⟨((-24997739/1073741824), (-26848837/8589934592)), (211/34359738368), by norm_num⟩
  | 7 => ⟨((1004354679/137438953472), (67420485/68719476736)), (267/137438953472), by norm_num⟩
  | 8 => ⟨((-1103396393/549755813888), (-148137947/549755813888)), (295/549755813888), by norm_num⟩
  | 9 => ⟨((1077515411/2199023255552), (144663261/2199023255552)), (145/1099511627776), by norm_num⟩
  | 10 => ⟨((-473508669/4398046511104), (-127143069/8796093022208)), (257/8796093022208), by norm_num⟩
  | 11 => ⟨((1513316197/70368744177664), (101586137/35184372088832)), (413/70368744177664), by norm_num⟩
  | 12 => ⟨((-1108365181/281474976710656), (-74402519/140737488355328)), (19/17592186044416), by norm_num⟩
  | 13 => ⟨((1498662903/2251799813685248), (12575311/140737488355328)), (207/1125899906842624), by norm_num⟩
  | 14 => ⟨((-1881656551/18014398509481984), (-31578037/2251799813685248)), (261/9007199254740992), by norm_num⟩
  | 15 => ⟨((1102512539/72057594037927936), (148019283/72057594037927936)), (77/18014398509481984), by norm_num⟩
  | 16 => ⟨((-37851057/18014398509481984), (-162615803/576460752303423488)), (85/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-3918430862763/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779034348127921/633825300114114700748351602688), (-4638633050687/633825300114114700748351602688)), (138985/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890039967078883/39614081257132168796771975168), (-5217562154793/39614081257132168796771975168)), (156401/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889832829449157/2475880078570760549798248448), (-173205759607/77371252455336267181195264)), (41557/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442874532717255/38685626227668133590597632), (-2770687149163/77371252455336267181195264)), (166285/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549840646851657/9671406556917033397649408), (-162304776059/302231454903657293676544)), (155953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259038996255859/604462909807314587353088), (-4543248230325/604462909807314587353088)), (17065/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((118012307362037/4722366482869645213696), (-7380368215425/75557863725914323419136)), (221959/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297841459327553/4722366482869645213696), (-5533167425539/4722366482869645213696)), (83285/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405465173988481/147573952589676412928), (-7604678802115/590295810358705651712)), (229195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455996583305493/18446744073709551616), (-9500709397197/73786976294838206464)), (143369/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823227049896937/9223372036854775808), (-5340616314815/4611686018427387904)), (80729/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594468657621655/1152921504606846976), (-1334050259575/144115188075855872)), (40417/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194995464201641/144115188075855872), (-4664209588187/72057594037927936)), (1107/562949953421312), by norm_num⟩
  | 4 => ⟨((373060999760897/9007199254740992), (-13972767851297/36028797018963968)), (213017/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489988966367511/9007199254740992), (-1089450821985/562949953421312)), (534201/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114665052335047/2251799813685248), (-17379113298663/2251799813685248)), (536693/2251799813685248), by norm_num⟩
  | 1 => ⟨((138623535859781/140737488355328), (-810577875389/35184372088832)), (202821/281474976710656), by norm_num⟩
  | 0 => ⟨((545921226520925/562949953421312), (-3209794504625/70368744177664)), (823815/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((545921226520925/562949953421312), (-3209794504625/70368744177664)), (3142604830028343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1056472625284315/1125899906842624), (-12450804496531/140737488355328)), (836473/281474976710656), by norm_num⟩
  | 2 => ⟨((982514483894227/1125899906842624), (-186928646618183/1125899906842624)), (6871155/1125899906842624), by norm_num⟩
  | 3 => ⟨((826354444547869/1125899906842624), (-163122939828773/562949953421312)), (14273783/1125899906842624), by norm_num⟩
  | 4 => ⟨((1023937013454363/2251799813685248), (-957792894490845/2251799813685248)), (58449129/2251799813685248), by norm_num⟩
  | 5 => ⟨((116422230775627/4503599627370496), (-435526990424491/1125899906842624)), (25719513/562949953421312), by norm_num⟩
  | 6 => ⟨((-1341764927783667/9007199254740992), (-90070215798147/4503599627370496)), (339642939/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1998394667/33554432)), (3/33554432), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-33319209/16777216), (-523555241/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1129163764525565/9007199254740992), (503176875314877/9007199254740992)), (109669305/4503599627370496), by norm_num⟩
  | 1 => ⟨((-619887269/2147483648), (-276233571/2147483648)), (243/4294967296), by norm_num⟩
  | 2 => ⟨((1427343185/4294967296), (636051303/4294967296)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((-273881595/1073741824), (-61023427/536870912)), (219/4294967296), by norm_num⟩
  | 4 => ⟨((315317839/2147483648), (562046533/8589934592)), (255/8589934592), by norm_num⟩
  | 5 => ⟨((-1161673849/17179869184), (-517663987/17179869184)), (237/17179869184), by norm_num⟩
  | 6 => ⟨((891617629/34359738368), (397321793/34359738368)), (23/4294967296), by norm_num⟩
  | 7 => ⟨((-1173157407/137438953472), (-522781279/137438953472)), (245/137438953472), by norm_num⟩
  | 8 => ⟨((1350647379/549755813888), (300937095/274877906944)), (71/137438953472), by norm_num⟩
  | 9 => ⟨((-1382213565/2199023255552), (-153985171/549755813888)), (293/2199023255552), by norm_num⟩
  | 10 => ⟨((318266435/2199023255552), (567302335/8796093022208)), (17/549755813888), by norm_num⟩
  | 11 => ⟨((-1065942617/35184372088832), (-475004327/35184372088832)), (115/17592186044416), by norm_num⟩
  | 12 => ⟨((818141193/140737488355328), (182289647/70368744177664)), (179/140737488355328), by norm_num⟩
  | 13 => ⟨((-1159285979/1125899906842624), (-258299953/562949953421312)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((762672747/4503599627370496), (169930749/2251799813685248)), (85/2251799813685248), by norm_num⟩
  | 15 => ⟨((-468298373/18014398509481984), (-13042667/1125899906842624)), (211/36028797018963968), by norm_num⟩
  | 16 => ⟨((1078296853/288230376151711744), (240254805/144115188075855872)), (245/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806918929/10141204801825835211973625643008), (273030496705/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444726379115603/158456325028528675187087900672), (646329332013/633825300114114700748351602688)), (184527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944947850535661/19807040628566084398385987584), (726994187759/39614081257132168796771975168)), (103801/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889680409997717/2475880078570760549798248448), (772274865503/2475880078570760549798248448)), (110293/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771346681871005/154742504910672534362390528), (386049455435/77371252455336267181195264)), (220597/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774849846966559/4835703278458516698824704), (723655833075/9671406556917033397649408)), (206821/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258916692306257/604462909807314587353088), (39563251313/37778931862957161709568)), (45245/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236000012930325/9444732965739290427392), (514147178037/37778931862957161709568)), (294113/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648847767764663/2361183241434822606848), (96364311859/590295810358705651712)), (55151/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810831394704873/295147905179352825856), (1059509988571/590295810358705651712)), (1185/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1823743053444129/73786976294838206464), (1323641760877/73786976294838206464)), (379245/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455739748707423/2305843009213693952), (1488072320587/9223372036854775808)), (213357/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797103817336109/576460752303423488), (371698140285/288230376151711744)), (426793/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194774964816389/144115188075855872), (324876306527/36028797018963968)), (373533/144115188075855872), by norm_num⟩
  | 4 => ⟨((745964501400229/18014398509481984), (1946384966603/36028797018963968)), (140119/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489622701872723/9007199254740992), (1213980949513/4503599627370496)), (700907/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114339836000549/2251799813685248), (4840898686497/4503599627370496)), (10959/35184372088832), by norm_num⟩
  | 1 => ⟨((1108602478216257/1125899906842624), (1805974965185/562949953421312)), (2106487/2251799813685248), by norm_num⟩
  | 0 => ⟨((272868820182259/281474976710656), (14298692736353/2251799813685248)), (4222487/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272868820182259/281474976710656), (14298692736353/2251799813685248)), (16107509621627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((66128612324303/70368744177664), (13861507202923/1125899906842624)), (8240393/2251799813685248), by norm_num⟩
  | 2 => ⟨((248533229731991/281474976710656), (52105078569447/2251799813685248)), (7845313/1125899906842624), by norm_num⟩
  | 3 => ⟨((1754368251903763/2251799813685248), (11501771501713/281474976710656)), (7108691/562949953421312), by norm_num⟩
  | 4 => ⟨((681530688647957/1125899906842624), (143375748701095/2251799813685248)), (46630655/2251799813685248), by norm_num⟩
  | 5 => ⟨((1631921009846091/4503599627370496), (347153320304279/4503599627370496)), (15597779/562949953421312), by norm_num⟩
  | 6 => ⟨((1129163764525565/9007199254740992), (503176875314877/9007199254740992)), (109669305/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33319209/16777216), (-523555241/8388608)), (1/8388608), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-272613299/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-636735809176591/9007199254740992), (-471985526995611/4503599627370496)), (51296349/1125899906842624), by norm_num⟩
  | 1 => ⟨((728047269/4294967296), (1079341759/4294967296)), (59/536870912), by norm_num⟩
  | 2 => ⟨((-109111319/536870912), (-647037125/2147483648)), (285/2147483648), by norm_num⟩
  | 3 => ⟨((697700043/4294967296), (1034351509/4294967296)), (229/2147483648), by norm_num⟩
  | 4 => ⟨((-836505817/8589934592), (-1240133297/8589934592)), (69/1073741824), by norm_num⟩
  | 5 => ⟨((401170669/8589934592), (297370977/4294967296)), (133/4294967296), by norm_num⟩
  | 6 => ⟨((-641310167/34359738368), (-950752613/34359738368)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((439369891/68719476736), (651372913/68719476736)), (295/68719476736), by norm_num⟩
  | 8 => ⟨((-131695373/68719476736), (-390481007/137438953472)), (89/68719476736), by norm_num⟩
  | 9 => ⟨((561407489/1099511627776), (416147805/549755813888)), (191/549755813888), by norm_num⟩
  | 10 => ⟨((-269239273/2199023255552), (-199575771/1099511627776)), (369/4398046511104), by norm_num⟩
  | 11 => ⟨((469532785/17592186044416), (21752809/549755813888)), (81/4398046511104), by norm_num⟩
  | 12 => ⟨((-375296815/70368744177664), (-1112767101/140737488355328)), (521/140737488355328), by norm_num⟩
  | 13 => ⟨((138449609/140737488355328), (205253767/140737488355328)), (193/281474976710656), by norm_num⟩
  | 14 => ⟨((-47426809/281474976710656), (-562488043/2251799813685248)), (531/4503599627370496), by norm_num⟩
  | 15 => ⟨((485224623/18014398509481984), (359676645/9007199254740992)), (171/9007199254740992), by norm_num⟩
  | 16 => ⟨((-581758915/144115188075855872), (-862466927/144115188075855872)), (103/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-2819141208443/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889386523353095/316912650057057350374175801344), (-1668171240325/316912650057057350374175801344)), (5783/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889746374215607/39614081257132168796771975168), (-3752695466273/39614081257132168796771975168)), (208231/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944760680068947/1237940039285380274899124224), (-3986396498943/2475880078570760549798248448)), (110647/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885593596771151/77371252455336267181195264), (-3985448923373/154742504910672534362390528)), (221349/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549549708060197/9671406556917033397649408), (-466918971281/1208925819614629174706176)), (207573/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314696247362423/151115727451828646838272), (-204214152027/37778931862957161709568)), (181685/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887785214754381/75557863725914323419136), (-5307681501845/75557863725914323419136)), (295347/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297533607146715/4722366482869645213696), (-3979110968313/4722366482869645213696)), (221607/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621438901230827/590295810358705651712), (-5468596986685/590295810358705651712)), (304865/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823461340654661/73786976294838206464), (-3415863468791/36893488147419103232)), (381315/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822639524581923/9223372036854775808), (-3840084433697/4611686018427387904)), (214651/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398471247774125/288230376151711744), (-959158479693/144115188075855872)), (53713/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194489089757357/144115188075855872), (-3353175525647/72057594037927936)), (376445/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491493086481291/36028797018963968), (-2511005836481/9007199254740992)), (565575/36028797018963968), by norm_num⟩
  | 3 => ⟨((744532710078625/4503599627370496), (-12527928643367/9007199254740992)), (44285/562949953421312), by norm_num⟩
  | 2 => ⟨((278441016258481/562949953421312), (-6243669039435/1125899906842624)), (710949/2251799813685248), by norm_num⟩
  | 1 => ⟨((553846456759967/562949953421312), (-4657435405273/281474976710656)), (268103/281474976710656), by norm_num⟩
  | 0 => ⟨((544737200221037/562949953421312), (-18427843601711/562949953421312)), (2168861/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544737200221037/562949953421312), (-18427843601711/562949953421312)), (8273548130515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1053020894960515/1125899906842624), (-71326638318021/1125899906842624)), (1084845/281474976710656), by norm_num⟩
  | 2 => ⟨((490170355811201/562949953421312), (-133419392007581/1125899906842624)), (17333589/2251799813685248), by norm_num⟩
  | 3 => ⟨((1675579100713955/2251799813685248), (-464682378637847/2251799813685248)), (34293387/2251799813685248), by norm_num⟩
  | 4 => ⟨((575458705072775/1125899906842624), (-43221653040805/140737488355328)), (65189469/2251799813685248), by norm_num⟩
  | 5 => ⟨((375865736016103/2251799813685248), (-1413825230540989/4503599627370496)), (53339219/1125899906842624), by norm_num⟩
  | 6 => ⟨((-636735809176591/9007199254740992), (-471985526995611/4503599627370496)), (51296349/1125899906842624), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-272613299/4194304)), (1/8388608), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-565010997/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-199166286177561/9007199254740992), (129671881752643/1125899906842624)), (357614875/9007199254740992), by norm_num⟩
  | 1 => ⟨((235991301/4294967296), (-614590685/2147483648)), (213/2147483648), by norm_num⟩
  | 2 => ⟨((-293208177/4294967296), (47725015/134217728)), (133/1073741824), by norm_num⟩
  | 3 => ⟨((242864983/4294967296), (-632491771/2147483648)), (443/4294967296), by norm_num⟩
  | 4 => ⟨((-150874203/4294967296), (1571683007/8589934592)), (553/8589934592), by norm_num⟩
  | 5 => ⟨((37490831/2147483648), (-781097111/8589934592)), (69/2147483648), by norm_num⟩
  | 6 => ⟨((-248429907/34359738368), (1293968937/34359738368)), (115/8589934592), by norm_num⟩
  | 7 => ⟨((11023663/4294967296), (-918683433/68719476736)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((-54785547/68719476736), (570710643/137438953472)), (205/137438953472), by norm_num⟩
  | 9 => ⟨((7563165/34359738368), (-1260589041/1099511627776)), (455/1099511627776), by norm_num⟩
  | 10 => ⟨((-240560115/4398046511104), (313244609/1099511627776)), (227/2199023255552), by norm_num⟩
  | 11 => ⟨((108685351/8796093022208), (-141524293/2199023255552)), (413/17592186044416), by norm_num⟩
  | 12 => ⟨((-90024317/35184372088832), (937799085/70368744177664)), (43/8796093022208), by norm_num⟩
  | 13 => ⟨((2150981/4398046511104), (-1434057343/562949953421312)), (33/35184372088832), by norm_num⟩
  | 14 => ⟨((-97736905/1125899906842624), (1018142465/2251799813685248)), (377/2251799813685248), by norm_num⟩
  | 15 => ⟨((16191139/1125899906842624), (-1349327457/18014398509481984)), (251/9007199254740992), by norm_num⟩
  | 16 => ⟨((-40233469/18014398509481984), (1676476385/144115188075855872)), (313/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (1146610122637/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778659377422181/633825300114114700748351602688), (1356799810685/316912650057057350374175801344)), (92467/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944809317396931/19807040628566084398385987584), (190763935599/2475880078570760549798248448)), (208085/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889385814902263/2475880078570760549798248448), (405284667599/309485009821345068724781056)), (110565/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885525924158543/77371252455336267181195264), (405184911117/19342813113834066795298816)), (221175/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549423034306561/9671406556917033397649408), (3038039119399/9671406556917033397649408)), (207399/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314668590544937/151115727451828646838272), (664359189633/151115727451828646838272)), (90761/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887605843159397/75557863725914323419136), (1079186560239/18889465931478580854784)), (147531/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648699713088599/2361183241434822606848), (1618085133383/2361183241434822606848)), (221375/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621254966934319/590295810358705651712), (555934660859/73786976294838206464)), (76129/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911616134340275/36893488147419103232), (1388990764195/18446744073709551616)), (95209/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455595745060917/2305843009213693952), (3122904402771/4611686018427387904)), (428703/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796814948294023/576460752303423488), (6240000887971/1152921504606846976)), (214515/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194267510083617/144115188075855872), (1363368134473/36028797018963968)), (375771/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491163965427735/36028797018963968), (8167166491779/36028797018963968)), (564395/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488659686595771/9007199254740992), (10186165910101/9007199254740992)), (176697/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113366799073031/2251799813685248), (5076020622969/1125899906842624)), (1417465/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214236129437175/2251799813685248), (30285945459549/2251799813685248)), (2135947/2251799813685248), by norm_num⟩
  | 0 => ⟨((272102048063061/281474976710656), (14973461100067/562949953421312)), (538879/281474976710656), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((272102048063061/281474976710656), (14973461100067/562949953421312)), (2055660248876476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2102736784359637/2251799813685248), (14474854850451/281474976710656)), (133817/35184372088832), by norm_num⟩
  | 2 => ⟨((1957586365555583/2251799813685248), (216266540621105/2251799813685248)), (16875549/2251799813685248), by norm_num⟩
  | 3 => ⟨((1681043376507717/2251799813685248), (94004899696853/562949953421312)), (4072849/281474976710656), by norm_num⟩
  | 4 => ⟨((596082315735429/1125899906842624), (561422247339277/2251799813685248)), (3720627/140737488355328), by norm_num⟩
  | 5 => ⟨((982380016199047/4503599627370496), (1188929393334295/4503599627370496)), (92717909/2251799813685248), by norm_num⟩
  | 6 => ⟨((-199166286177561/9007199254740992), (129671881752643/1125899906842624)), (357614875/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-565010997/8388608)), (1/8388608), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-4556335/65536)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((904496281915519/9007199254740992), (-392172360902647/9007199254740992)), (87100205/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1106256083/4294967296), (29978223/268435456)), (215/4294967296), by norm_num⟩
  | 2 => ⟨((1418745415/4294967296), (-615140991/4294967296)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((-303250845/1073741824), (525935163/4294967296)), (15/268435456), by norm_num⟩
  | 4 => ⟨((194455765/1073741824), (-337249265/4294967296)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((-798030703/8589934592), (173005457/4294967296)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((1364605559/34359738368), (-591666981/34359738368)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-500020593/34359738368), (108399703/17179869184)), (207/68719476736), by norm_num⟩
  | 8 => ⟨((1282527499/274877906944), (-556079497/274877906944)), (67/68719476736), by norm_num⟩
  | 9 => ⟨((-731026241/549755813888), (633918111/1099511627776)), (77/274877906944), by norm_num⟩
  | 10 => ⟨((750018115/2199023255552), (-162596785/1099511627776)), (5/68719476736), by norm_num⟩
  | 11 => ⟨((-699548539/8796093022208), (303310923/8796093022208)), (301/17592186044416), by norm_num⟩
  | 12 => ⟨((37381387/2199023255552), (-259325719/35184372088832)), (259/70368744177664), by norm_num⟩
  | 13 => ⟨((-944062667/281474976710656), (51165949/35184372088832)), (207/281474976710656), by norm_num⟩
  | 14 => ⟨((691849409/1125899906842624), (-299972727/1125899906842624)), (305/2251799813685248), by norm_num⟩
  | 15 => ⟨((-946431305/9007199254740992), (410354589/9007199254740992)), (211/9007199254740992), by norm_num⟩
  | 16 => ⟨((151721773/9007199254740992), (-263134685/36028797018963968)), (273/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-133229909531/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889278349911349/316912650057057350374175801344), (-630539411085/633825300114114700748351602688)), (46131/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472375838726759/9903520314283042199192993792), (-177305074567/9903520314283042199192993792)), (103799/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889263632234775/2475880078570760549798248448), (-188344141947/618970019642690137449562112)), (110291/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221366250670263/19342813113834066795298816), (-753185395925/154742504910672534362390528)), (13787/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((193663645906863/1208925819614629174706176), (-176477064121/2417851639229258349412352)), (206817/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258575088973963/604462909807314587353088), (-308733374323/302231454903657293676544)), (11311/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943722599765429/37778931862957161709568), (-1003003049285/75557863725914323419136)), (147053/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297279533830727/4722366482869645213696), (-375959792047/2361183241434822606848)), (110299/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810545536653115/295147905179352825856), (-1033349089991/590295810358705651712)), (37919/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455757209350051/18446744073709551616), (-1290876386981/73786976294838206464)), (189617/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911078045673165/4611686018427387904), (-725561541201/4611686018427387904)), (106675/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796702733753611/576460752303423488), (-1449733310153/1152921504606846976)), (426777/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194073896027093/144115188075855872), (-1266954929951/144115188075855872)), (373517/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490879052383879/36028797018963968), (-1897313399985/36028797018963968)), (280225/18014398509481984), by norm_num⟩
  | 3 => ⟨((186039143908477/1125899906842624), (-73943546225/281474976710656)), (175217/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226069213363851/4503599627370496), (-2358040976411/2251799813685248)), (701329/2251799813685248), by norm_num⟩
  | 1 => ⟨((553327701549017/562949953421312), (-7033499403463/2251799813685248)), (2106307/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087624000394641/1125899906842624), (-1738166994377/281474976710656)), (4221987/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087624000394641/1125899906842624), (-1738166994377/281474976710656)), (16105602272994231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((525303190564957/562949953421312), (-13432612460763/1125899906842624)), (4104529/1125899906842624), by norm_num⟩
  | 2 => ⟨((61261736405603/70368744177664), (-50137275190291/2251799813685248)), (969753/140737488355328), by norm_num⟩
  | 3 => ⟨((1705550638233249/2251799813685248), (-87297182085501/2251799813685248)), (27706917/2251799813685248), by norm_num⟩
  | 4 => ⟨((1288428111568939/2251799813685248), (-66120337925697/1125899906842624)), (22059815/1125899906842624), by norm_num⟩
  | 5 => ⟨((729442907113173/2251799813685248), (-302660304391743/4503599627370496)), (55670475/2251799813685248), by norm_num⟩
  | 6 => ⟨((904496281915519/9007199254740992), (-392172360902647/9007199254740992)), (87100205/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-4556335/65536)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1200122679/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-692991735548213/9007199254740992), (-612407686392357/9007199254740992)), (168786507/4503599627370496), by norm_num⟩
  | 1 => ⟨((436030607/2147483648), (385327099/2147483648)), (427/4294967296), by norm_num⟩
  | 2 => ⟨((-575354885/2147483648), (-63556269/268435456)), (71/536870912), by norm_num⟩
  | 3 => ⟨((1012263017/4294967296), (894552733/4294967296)), (251/2147483648), by norm_num⟩
  | 4 => ⟨((-667855033/4294967296), (-590193987/4294967296)), (167/2147483648), by norm_num⟩
  | 5 => ⟨((44062693/536870912), (623022307/8589934592)), (177/4294967296), by norm_num⟩
  | 6 => ⟨((-620181189/17179869184), (-274031931/8589934592)), (313/17179869184), by norm_num⟩
  | 7 => ⟨((467626775/34359738368), (413249129/34359738368)), (237/34359738368), by norm_num⟩
  | 8 => ⟨((-308523467/68719476736), (-545294071/137438953472)), (157/68719476736), by norm_num⟩
  | 9 => ⟨((723743215/549755813888), (639583251/549755813888)), (185/274877906944), by norm_num⟩
  | 10 => ⟨((-381999967/1099511627776), (-337579373/1099511627776)), (393/2199023255552), by norm_num⟩
  | 11 => ⟨((733178045/8796093022208), (647920959/8796093022208)), (379/8796093022208), by norm_num⟩
  | 12 => ⟨((-322483149/17592186044416), (-142491713/8796093022208)), (335/35184372088832), by norm_num⟩
  | 13 => ⟨((523724011/140737488355328), (231411569/70368744177664)), (273/140737488355328), by norm_num⟩
  | 14 => ⟨((-789792965/1125899906842624), (-348976227/562949953421312)), (207/562949953421312), by norm_num⟩
  | 15 => ⟨((277907855/2251799813685248), (491183077/4503599627370496)), (585/9007199254740992), by norm_num⟩
  | 16 => ⟨((-366707381/18014398509481984), (-324065075/18014398509481984)), (97/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-3149516439683/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778450969298437/633825300114114700748351602688), (-931512259341/158456325028528675187087900672)), (185133/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889384026409301/39614081257132168796771975168), (-4190959184929/39614081257132168796771975168)), (104161/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889136342368257/2475880078570760549798248448), (-4451858601283/2475880078570760549798248448)), (221397/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885401074883637/77371252455336267181195264), (-4450693837507/154742504910672534362390528)), (221459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48412146936885/302231454903657293676544), (-4171288182097/9671406556917033397649408)), (207683/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629234540845111/302231454903657293676544), (-3648640173235/604462909807314587353088)), (45447/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887271813410937/75557863725914323419136), (-2963360789811/37778931862957161709568)), (295527/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297148511523827/4722366482869645213696), (-1110753241921/1180591620717411303424)), (221753/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620909322651661/590295810358705651712), (-1526462047841/147573952589676412928)), (305085/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911399629993577/36893488147419103232), (-7627370404261/73786976294838206464)), (381617/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821894537236935/9223372036854775808), (-8574002883517/9223372036854775808)), (429679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199142477777193/144115188075855872), (-4282761017725/576460752303423488)), (430129/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298459216276881/36028797018963968), (-7485297948831/144115188075855872)), (376871/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490514351594469/36028797018963968), (-11208897067777/36028797018963968)), (566321/36028797018963968), by norm_num⟩
  | 3 => ⟨((371960329582021/2251799813685248), (-13977824169057/9007199254740992)), (709679/9007199254740992), by norm_num⟩
  | 2 => ⟨((556269482267813/1125899906842624), (-6963979305711/1125899906842624)), (712353/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105852857265489/1125899906842624), (-10383777407523/562949953421312)), (1075229/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085785209701989/1125899906842624), (-41039262943809/1125899906842624)), (2177357/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085785209701989/1125899906842624), (-41039262943809/1125899906842624)), (8305957798484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2091207741203187/2251799813685248), (-158308298812879/2251799813685248)), (8716581/2251799813685248), by norm_num⟩
  | 2 => ⟨((482734774309169/562949953421312), (-36754548290907/281474976710656)), (8707741/1125899906842624), by norm_num⟩
  | 3 => ⟨((1617403278310191/2251799813685248), (-63034727922849/281474976710656)), (34416045/2251799813685248), by norm_num⟩
  | 4 => ⟨((1048804261897403/2251799813685248), (-362208309886849/1125899906842624)), (16213669/562949953421312), by norm_num⟩
  | 5 => ⟨((127722486091787/1125899906842624), (-1349624835370315/4503599627370496)), (204284001/4503599627370496), by norm_num⟩
  | 6 => ⟨((-692991735548213/9007199254740992), (-612407686392357/9007199254740992)), (168786507/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1200122679/16777216)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-307874371/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-179430028361915/4503599627370496), (794062151902519/9007199254740992)), (77318181/2251799813685248), by norm_num⟩
  | 1 => ⟨((463395619/4294967296), (-64085727/268435456)), (201/2147483648), by norm_num⟩
  | 2 => ⟨((-156862325/1073741824), (1388378927/4294967296)), (547/4294967296), by norm_num⟩
  | 3 => ⟨((141597017/1073741824), (-1253266611/4294967296)), (31/268435456), by norm_num⟩
  | 4 => ⟨((-191725915/2147483648), (106059653/536870912)), (169/2147483648), by norm_num⟩
  | 5 => ⟨((207681361/4294967296), (-919087567/8589934592)), (23/536870912), by norm_num⟩
  | 6 => ⟨((-187470517/8589934592), (414822545/8589934592)), (167/8589934592), by norm_num⟩
  | 7 => ⟨((72525653/8589934592), (-320960079/17179869184)), (519/68719476736), by norm_num⟩
  | 8 => ⟨((-196403109/68719476736), (434588003/68719476736)), (353/137438953472), by norm_num⟩
  | 9 => ⟨((236386435/274877906944), (-1046121003/549755813888)), (427/549755813888), by norm_num⟩
  | 10 => ⟨((-256058533/1099511627776), (1133179277/2199023255552)), (465/2199023255552), by norm_num⟩
  | 11 => ⟨((252152495/4398046511104), (-1115893225/8796093022208)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((-455227743/35184372088832), (1007298291/35184372088832)), (417/35184372088832), by norm_num⟩
  | 13 => ⟨((189658397/70368744177664), (-839327489/140737488355328)), (349/140737488355328), by norm_num⟩
  | 14 => ⟨((-293488263/562949953421312), (649411707/562949953421312)), (271/562949953421312), by norm_num⟩
  | 15 => ⟨((423883173/4503599627370496), (-937941069/4503599627370496)), (393/4503599627370496), by norm_num⟩
  | 16 => ⟨((-71743557/4503599627370496), (634997875/18014398509481984)), (267/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (2599040598961/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778361643285103/633825300114114700748351602688), (3074504145421/633825300114114700748351602688)), (185005/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889283688619825/39614081257132168796771975168), (3458106827043/39614081257132168796771975168)), (104085/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944514966740225/1237940039285380274899124224), (918340582061/618970019642690137449562112)), (110613/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885347982863907/77371252455336267181195264), (3672376901789/154742504910672534362390528)), (55319/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774544696598093/4835703278458516698824704), (1720903306971/4835703278458516698824704)), (207501/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314595606272493/151115727451828646838272), (188158398449/37778931862957161709568)), (181617/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117945715214333/4722366482869645213696), (2445078507951/37778931862957161709568)), (73807/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297043624802655/4722366482869645213696), (1832951132375/2361183241434822606848)), (110755/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810382868869421/295147905179352825856), (2518914601629/295147905179352825856)), (19045/36893488147419103232), by norm_num⟩
  | 8 => ⟨((911310364588681/36893488147419103232), (3146554556797/36893488147419103232)), (95279/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910847497447273/4611686018427387904), (442125466035/576460752303423488)), (107263/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592941908070605/1152921504606846976), (1766709376983/288230376151711744)), (26839/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193665518064443/144115188075855872), (6175424079009/144115188075855872)), (376165/144115188075855872), by norm_num⟩
  | 4 => ⟨((372565244250373/9007199254740992), (4623518629023/18014398509481984)), (141271/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487530958745761/9007199254740992), (720666589857/562949953421312)), (44239/562949953421312), by norm_num⟩
  | 2 => ⟨((2224476198877513/4503599627370496), (22977104829955/4503599627370496)), (355015/1125899906842624), by norm_num⟩
  | 1 => ⟨((552712571967037/562949953421312), (17127838662455/1125899906842624)), (1070577/1125899906842624), by norm_num⟩
  | 0 => ⟨((135627901472483/140737488355328), (67674941613165/2251799813685248)), (4326731/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((135627901472483/140737488355328), (67674941613165/2251799813685248)), (16505168923384856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089227272375825/2251799813685248), (130435897649283/2251799813685248)), (8599361/2251799813685248), by norm_num⟩
  | 2 => ⟨((965418205876779/1125899906842624), (242037709577495/2251799813685248)), (16953271/2251799813685248), by norm_num⟩
  | 3 => ⟨((814803113001935/1125899906842624), (415077059540945/2251799813685248)), (32718117/2251799813685248), by norm_num⟩
  | 4 => ⟨((1102818941266923/2251799813685248), (300387341889109/1125899906842624)), (7427191/281474976710656), by norm_num⟩
  | 5 => ⟨((759640702828327/4503599627370496), (294229396715313/1125899906842624)), (22476093/562949953421312), by norm_num⟩
  | 6 => ⟨((-179430028361915/4503599627370496), (794062151902519/9007199254740992)), (77318181/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-307874371/4194304)), (1/8388608), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile040Terms1

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
namespace Reinmann.XiBand58.Tile003Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2501/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2501/160))
  have he : value ((15/16), (2501/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-69118709/33554432), (-1152439271/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1096073652943/8796093022208), (-120876768070109/4503599627370496)), (196453915/9007199254740992), by norm_num⟩
  | 1 => ⟨((1175937485/4294967296), (126644805/2147483648)), (13/268435456), by norm_num⟩
  | 2 => ⟨((-322974843/1073741824), (-139133539/2147483648)), (231/4294967296), by norm_num⟩
  | 3 => ⟨((236549421/1073741824), (6368909/134217728)), (171/4294967296), by norm_num⟩
  | 4 => ⟨((-1039504403/8589934592), (-111951387/4294967296)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((913609849/17179869184), (196785871/17179869184)), (169/17179869184), by norm_num⟩
  | 6 => ⟨((-1338270677/68719476736), (-4503987/1073741824)), (125/34359738368), by norm_num⟩
  | 7 => ⟨((1680274985/274877906944), (180960383/137438953472)), (317/274877906944), by norm_num⟩
  | 8 => ⟨((-461492687/274877906944), (-198805301/549755813888)), (11/34359738368), by norm_num⟩
  | 9 => ⟨((450668033/1099511627776), (194142175/2199023255552)), (87/1099511627776), by norm_num⟩
  | 10 => ⟨((-792175103/8796093022208), (-341259167/17592186044416)), (77/4398046511104), by norm_num⟩
  | 11 => ⟨((79117573/4398046511104), (34082865/8796093022208)), (31/8796093022208), by norm_num⟩
  | 12 => ⟨((-463570869/140737488355328), (-49925139/70368744177664)), (23/35184372088832), by norm_num⟩
  | 13 => ⟨((626811881/1125899906842624), (270022751/2251799813685248)), (251/2251799813685248), by norm_num⟩
  | 14 => ⟨((-786997983/9007199254740992), (-339028929/18014398509481984)), (159/9007199254740992), by norm_num⟩
  | 15 => ⟨((922246033/72057594037927936), (49661513/18014398509481984)), (47/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1013190825/576460752303423488), (-109117497/288230376151711744)), (13/36028797018963968), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-3815922869959/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889390431548655/316912650057057350374175801344), (-4516056040745/633825300114114700748351602688)), (92645/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889754884953367/39614081257132168796771975168), (-2539809308887/19807040628566084398385987584)), (52127/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944765017626141/1237940039285380274899124224), (-2697978680887/1237940039285380274899124224)), (110803/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442798863863969/38685626227668133590597632), (-1348669440711/38685626227668133590597632)), (13855/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549557014854645/9671406556917033397649408), (-5056150972389/9671406556917033397649408)), (6497/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258790944455877/604462909807314587353088), (-2211386415805/302231454903657293676544)), (45499/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887794070226151/75557863725914323419136), (-3592228782111/37778931862957161709568)), (147945/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297539530673461/4722366482869645213696), (-2693056882533/2361183241434822606848)), (6939/295147905179352825856), by norm_num⟩
  | 9 => ⟨((202680735055125/73786976294838206464), (-1850571070811/147573952589676412928)), (152763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911734159185517/36893488147419103232), (-1155927908539/9223372036854775808)), (191113/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822644976867323/9223372036854775808), (-10395883898813/9223372036854775808)), (53805/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593887451589771/1152921504606846976), (-1298319070977/144115188075855872)), (53873/288230376151711744), by norm_num⟩
  | 5 => ⟨((597243942078371/72057594037927936), (-9077739564439/144115188075855872)), (188863/144115188075855872), by norm_num⟩
  | 4 => ⟨((745742289542631/18014398509481984), (-6797815526055/18014398509481984)), (283909/36028797018963968), by norm_num⟩
  | 3 => ⟨((744521551642131/4503599627370496), (-8478924211377/4503599627370496)), (355963/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113724305339367/2251799813685248), (-2112857038079/281474976710656)), (178791/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107589950364415/1125899906842624), (-6304239328391/281474976710656)), (135107/281474976710656), by norm_num⟩
  | 0 => ⟨((1089096876456989/1125899906842624), (-1558922905239/35184372088832)), (1097141/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1089096876456989/1125899906842624), (-1558922905239/35184372088832)), (4185260777000045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525643279973355/562949953421312), (-48254891758377/562949953421312)), (2219779/1125899906842624), by norm_num⟩
  | 2 => ⟨((973345220254395/1125899906842624), (-180228167171723/1125899906842624)), (4525899/1125899906842624), by norm_num⟩
  | 3 => ⟨((406305533906525/562949953421312), (-623232044005585/2251799813685248)), (18548565/2251799813685248), by norm_num⟩
  | 4 => ⟨((125062671854841/281474976710656), (-899627495653533/2251799813685248)), (18521007/1125899906842624), by norm_num⟩
  | 5 => ⟨((85120075485151/2251799813685248), (-1598860681618109/4503599627370496)), (15628521/562949953421312), by norm_num⟩
  | 6 => ⟨((-1096073652943/8796093022208), (-120876768070109/4503599627370496)), (196453915/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1152439271/33554432)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-9054133/4194304), (-301925155/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-17631998817887/1125899906842624), (257631559020021/2251799813685248)), (173863707/9007199254740992), by norm_num⟩
  | 1 => ⟨((38718393/1073741824), (-565737331/2147483648)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((-178304789/4294967296), (1302658345/4294967296)), (7/134217728), by norm_num⟩
  | 3 => ⟨((136853983/4294967296), (-999827229/4294967296)), (173/4294967296), by norm_num⟩
  | 4 => ⟨((-157558971/8589934592), (1151093637/8589934592)), (201/8589934592), by norm_num⟩
  | 5 => ⟨((145117175/17179869184), (-265049105/4294967296)), (187/17179869184), by norm_num⟩
  | 6 => ⟨((-27845387/8589934592), (101716353/4294967296)), (145/34359738368), by norm_num⟩
  | 7 => ⟨((73275855/68719476736), (-1070676837/137438953472)), (193/137438953472), by norm_num⟩
  | 8 => ⟨((-168723891/549755813888), (616331131/274877906944)), (225/549755813888), by norm_num⟩
  | 9 => ⟨((172667163/2199023255552), (-157683875/274877906944)), (29/274877906944), by norm_num⟩
  | 10 => ⟨((-79516167/4398046511104), (18154027/137438953472)), (27/1099511627776), by norm_num⟩
  | 11 => ⟨((133158357/35184372088832), (-243206935/8796093022208)), (91/17592186044416), by norm_num⟩
  | 12 => ⟨((-1596919/2199023255552), (186668221/35184372088832)), (141/140737488355328), by norm_num⟩
  | 13 => ⟨((2262795/17592186044416), (-264504285/281474976710656)), (101/562949953421312), by norm_num⟩
  | 14 => ⟨((-190547311/9007199254740992), (1392099711/9007199254740992)), (67/2251799813685248), by norm_num⟩
  | 15 => ⟨((117000373/36028797018963968), (-1709561623/72057594037927936)), (83/18014398509481984), by norm_num⟩
  | 16 => ⟨((-134701657/288230376151711744), (984102777/288230376151711744)), (193/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (1111667421687/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778635812797027/633825300114114700748351602688), (2630836192789/633825300114114700748351602688)), (92459/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889592143077185/39614081257132168796771975168), (1479564155213/19807040628566084398385987584)), (104033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944678845546907/1237940039285380274899124224), (1571690505003/1237940039285380274899124224)), (110555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885511875543951/77371252455336267181195264), (785650450065/38685626227668133590597632)), (110577/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193674590172509/1208925819614629174706176), (368170186797/1208925819614629174706176)), (12961/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629325683289261/302231454903657293676544), (1288181929119/302231454903657293676544)), (45375/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887568528165249/75557863725914323419136), (4185040320571/75557863725914323419136)), (147513/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297371486147339/4722366482869645213696), (1568711839161/2361183241434822606848)), (6917/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621216624428529/590295810358705651712), (4311754115871/590295810358705651712)), (38059/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911592226493477/36893488147419103232), (2693194590943/36893488147419103232)), (190387/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455582335501491/2305843009213693952), (6055148329223/9223372036854775808)), (26789/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593576451094251/1152921504606846976), (6049478093755/1152921504606846976)), (214471/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194220961731455/144115188075855872), (5286920006889/144115188075855872)), (187841/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491094574855449/36028797018963968), (1979411894017/9007199254740992)), (282119/36028797018963968), by norm_num⟩
  | 3 => ⟨((372143425540053/2251799813685248), (1234351209147/1125899906842624)), (353277/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113281941028567/2251799813685248), (19682997692747/4503599627370496)), (708439/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106993578688917/1125899906842624), (14679194483325/1125899906842624)), (533693/1125899906842624), by norm_num⟩
  | 0 => ⟨((2176340669943511/2251799813685248), (58055022861595/2251799813685248)), (2153747/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2176340669943511/2251799813685248), (58055022861595/2251799813685248)), (8215892800337981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((262739181853861/281474976710656), (112219129409565/2251799813685248)), (2137101/1125899906842624), by norm_num⟩
  | 2 => ⟨((1956411494405365/2251799813685248), (209498994148459/2251799813685248)), (4202705/1125899906842624), by norm_num⟩
  | 3 => ⟨((1680280850854129/2251799813685248), (364034349525617/2251799813685248)), (8084807/1125899906842624), by norm_num⟩
  | 4 => ⟨((1194965340062265/2251799813685248), (543280928298835/2251799813685248)), (29359439/2251799813685248), by norm_num⟩
  | 5 => ⟨((503058926469571/2251799813685248), (1153214198328741/4503599627370496)), (90654481/4503599627370496), by norm_num⟩
  | 6 => ⟨((-17631998817887/1125899906842624), (257631559020021/2251799813685248)), (173863707/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-301925155/8388608)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-75431263/33554432), (-39302831/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((928916168901527/9007199254740992), (204810609445779/9007199254740992)), (17974717/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1062127919/4294967296), (-234181591/4294967296)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((636717879/2147483648), (280771465/4294967296)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-1017855195/4294967296), (-112210095/2147483648)), (21/1073741824), by norm_num⟩
  | 4 => ⟨((152544385/1073741824), (33633507/1073741824)), (103/8589934592), by norm_num⟩
  | 5 => ⟨((-1170513471/17179869184), (-32259851/2147483648)), (101/17179869184), by norm_num⟩
  | 6 => ⟨((935589573/34359738368), (206281985/34359738368)), (83/34359738368), by norm_num⟩
  | 7 => ⟨((-1281969037/137438953472), (-17665807/8589934592)), (29/34359738368), by norm_num⟩
  | 8 => ⟨((1537013747/549755813888), (338886041/549755813888)), (141/549755813888), by norm_num⟩
  | 9 => ⟨((-1638043555/2199023255552), (-180580719/1099511627776)), (153/2199023255552), by norm_num⟩
  | 10 => ⟨((1571142759/8796093022208), (173205461/4398046511104)), (149/8796093022208), by norm_num⟩
  | 11 => ⟨((-1369976653/35184372088832), (-75514283/8796093022208)), (33/8796093022208), by norm_num⟩
  | 12 => ⟨((273755045/35184372088832), (120716895/70368744177664)), (107/140737488355328), by norm_num⟩
  | 13 => ⟨((-1615842285/1125899906842624), (-356266427/1125899906842624)), (5/35184372088832), by norm_num⟩
  | 14 => ⟨((1107034451/4503599627370496), (244082737/4503599627370496)), (7/281474976710656), by norm_num⟩
  | 15 => ⟨((-353940357/9007199254740992), (-312151915/36028797018963968)), (73/18014398509481984), by norm_num⟩
  | 16 => ⟨((848711909/144115188075855872), (374253801/288230376151711744)), (89/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (282681521053/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444625435856195/158456325028528675187087900672), (334443142891/633825300114114700748351602688)), (92233/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889441549554573/39614081257132168796771975168), (376175037507/39614081257132168796771975168)), (103765/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944598995130967/1237940039285380274899124224), (399594357215/2475880078570760549798248448)), (110253/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770864392861545/154742504910672534362390528), (24968207971/9671406556917033397649408)), (6891/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774623843417399/4835703278458516698824704), (374413688027/9671406556917033397649408)), (103367/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629260662444253/302231454903657293676544), (327502587683/604462909807314587353088)), (45225/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887357891509819/75557863725914323419136), (265993344799/37778931862957161709568)), (73493/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648607052034699/2361183241434822606848), (398810718317/4722366482869645213696)), (27561/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621001190605155/590295810358705651712), (68509193109/73786976294838206464)), (75797/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455729152184139/18446744073709551616), (684655435441/73786976294838206464)), (2961/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1822030005387423/9223372036854775808), (769637660047/9223372036854775808)), (26651/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796639797684939/576460752303423488), (96111092927/144115188075855872)), (213229/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193963998060625/144115188075855872), (167984025135/36028797018963968)), (186599/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490714684754323/36028797018963968), (1006223500957/36028797018963968)), (139973/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488108528324165/9007199254740992), (1254843743019/9007199254740992)), (350015/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112831234205261/2251799813685248), (312612820019/562949953421312)), (700281/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106353455119413/1125899906842624), (3729468241879/2251799813685248)), (1051057/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087032455189231/1125899906842624), (7371852861087/2251799813685248)), (2104701/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1087032455189231/1125899906842624), (7371852861087/2251799813685248)), (8028797158248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2098989378007367/2251799813685248), (14234734839535/2251799813685248)), (2038935/1125899906842624), by norm_num⟩
  | 2 => ⟨((1956458897694713/2251799813685248), (26537489740739/2251799813685248)), (7653837/2251799813685248), by norm_num⟩
  | 3 => ⟨((849770738222027/1125899906842624), (23056893250551/1125899906842624)), (13480357/2251799813685248), by norm_num⟩
  | 4 => ⟨((320445309048641/562949953421312), (34804289581251/1125899906842624)), (20900665/2251799813685248), by norm_num⟩
  | 5 => ⟨((1454940863936331/4503599627370496), (158491834143353/4503599627370496)), (3135819/281474976710656), by norm_num⟩
  | 6 => ⟨((928916168901527/9007199254740992), (204810609445779/9007199254740992)), (17974717/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-39302831/1048576)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-19542101/8388608), (-325831965/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((5682046844051/140737488355328), (-797736368599717/9007199254740992)), (30166203/2251799813685248), by norm_num⟩
  | 1 => ⟨((-430888549/4294967296), (945234493/4294967296)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((267679455/2147483648), (-587204869/2147483648)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-110859743/1073741824), (972766189/4294967296)), (153/4294967296), by norm_num⟩
  | 4 => ⟨((550952225/8589934592), (-604308293/4294967296)), (3/134217728), by norm_num⟩
  | 5 => ⟨((-547625939/17179869184), (300329939/4294967296)), (193/17179869184), by norm_num⟩
  | 6 => ⟨((453599779/34359738368), (-995055817/34359738368)), (81/17179869184), by norm_num⟩
  | 7 => ⟨((-322043745/68719476736), (1412926181/137438953472)), (233/137438953472), by norm_num⟩
  | 8 => ⟨((200062161/137438953472), (-109718427/34359738368)), (147/274877906944), by norm_num⟩
  | 9 => ⟨((-110474621/274877906944), (121173355/137438953472)), (41/274877906944), by norm_num⟩
  | 10 => ⟨((3431489/34359738368), (-481767161/2199023255552)), (165/4398046511104), by norm_num⟩
  | 11 => ⟨((-396889825/17592186044416), (870651943/17592186044416)), (151/17592186044416), by norm_num⟩
  | 12 => ⟨((657489443/140737488355328), (-360581467/35184372088832)), (253/140737488355328), by norm_num⟩
  | 13 => ⟨((-251353829/281474976710656), (68923945/35184372088832)), (195/562949953421312), by norm_num⟩
  | 14 => ⟨((356909029/2251799813685248), (-391473301/1125899906842624)), (35/562949953421312), by norm_num⟩
  | 15 => ⟨((-14781427/562949953421312), (1037626249/18014398509481984)), (47/4503599627370496), by norm_num⟩
  | 16 => ⟨((146921865/36028797018963968), (-1289202183/144115188075855872)), (59/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (-1488996121931/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778374434635199/633825300114114700748351602688), (-1761407962507/633825300114114700748351602688)), (46187/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944649133035341/19807040628566084398385987584), (-1981181788551/39614081257132168796771975168)), (25983/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944522834512235/1237940039285380274899124224), (-1052252714043/1237940039285380274899124224)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770711978884901/154742504910672534362390528), (-1051971447101/77371252455336267181195264)), (110455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774552350140995/4835703278458516698824704), (-985924483501/4835703278458516698824704)), (103567/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258396113301561/604462909807314587353088), (-862385285135/302231454903657293676544)), (90637/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943577119236779/37778931862957161709568), (-1400816376371/37778931862957161709568)), (147313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648530601657669/2361183241434822606848), (-262530692085/590295810358705651712)), (110511/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405197672716083/147573952589676412928), (-1443123784921/295147905179352825856)), (151993/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113915818307801/4611686018427387904), (-1802712965947/36893488147419103232)), (190053/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821733013375483/9223372036854775808), (-1013207327637/2305843009213693952)), (213895/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796490967041381/576460752303423488), (-506092433293/144115188075855872)), (214001/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193702793736623/144115188075855872), (-3538051088361/144115188075855872)), (187371/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490321382453517/36028797018963968), (-5297897554239/36028797018963968)), (281297/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487614295298063/9007199254740992), (-6606337342187/9007199254740992)), (352043/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224666236857247/4503599627370496), (-13164685835865/4503599627370496)), (705353/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105596661643549/1125899906842624), (-4906864526221/562949953421312)), (1061209/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170961817259137/2251799813685248), (-9694758886563/562949953421312)), (2135197/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2170961817259137/2251799813685248), (-9694758886563/562949953421312)), (8145130166060637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1046179009733627/1125899906842624), (-74773792030179/2251799813685248)), (4190633/2251799813685248), by norm_num⟩
  | 2 => ⟨((970861382766221/1125899906842624), (-138958660933783/2251799813685248)), (4033065/1125899906842624), by norm_num⟩
  | 3 => ⟨((1665768762365991/2251799813685248), (-239647586577823/2251799813685248)), (14906341/2251799813685248), by norm_num⟩
  | 4 => ⟨((150843482367255/281474976710656), (-177279286227677/1125899906842624)), (12613371/1125899906842624), by norm_num⟩
  | 5 => ⟨((590873400763121/2251799813685248), (-190009251967383/1125899906842624)), (34982395/2251799813685248), by norm_num⟩
  | 6 => ⟨((5682046844051/140737488355328), (-797736368599717/9007199254740992)), (30166203/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-325831965/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-40343165/16777216), (-672655039/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-149144669736957/2251799813685248), (-276406802091383/4503599627370496)), (148766201/9007199254740992), by norm_num⟩
  | 1 => ⟨((364826703/2147483648), (676125955/4294967296)), (23/536870912), by norm_num⟩
  | 2 => ⟨((-467881009/2147483648), (-867114417/4294967296)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((800060729/4294967296), (741368189/4294967296)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-1026057627/8589934592), (-475392965/4294967296)), (265/8589934592), by norm_num⟩
  | 5 => ⟨((1052714341/17179869184), (7620993/134217728)), (275/17179869184), by norm_num⟩
  | 6 => ⟨((-900052991/34359738368), (-834025007/34359738368)), (237/34359738368), by norm_num⟩
  | 7 => ⟨((82449655/8589934592), (152802279/17179869184)), (11/4294967296), by norm_num⟩
  | 8 => ⟨((-845916759/274877906944), (-783860215/274877906944)), (57/68719476736), by norm_num⟩
  | 9 => ⟨((482163033/549755813888), (446791501/549755813888)), (131/549755813888), by norm_num⟩
  | 10 => ⟨((-494689505/2199023255552), (-916798059/4398046511104)), (271/4398046511104), by norm_num⟩
  | 11 => ⟨((461401283/8796093022208), (427552835/8796093022208)), (255/17592186044416), by norm_num⟩
  | 12 => ⟨((-98622577/8796093022208), (-731100913/70368744177664)), (55/17592186044416), by norm_num⟩
  | 13 => ⟨((155668871/70368744177664), (72124493/35184372088832)), (11/17592186044416), by norm_num⟩
  | 14 => ⟨((-912646333/2251799813685248), (-845694501/2251799813685248)), (65/562949953421312), by norm_num⟩
  | 15 => ⟨((624237767/9007199254740992), (289221809/4503599627370496)), (179/9007199254740992), by norm_num⟩
  | 16 => ⟨((-400284565/36028797018963968), (-741839293/72057594037927936)), (29/9007199254740992), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (-1559390804255/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889126590389739/316912650057057350374175801344), (-1844452803621/316912650057057350374175801344)), (92563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889161570314503/39614081257132168796771975168), (-4149137880927/39614081257132168796771975168)), (104157/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888900050134495/2475880078570760549798248448), (-4407376192133/2475880078570760549798248448)), (55347/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110660370833023/9671406556917033397649408), (-4406158305801/154742504910672534362390528)), (110725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548967329592653/9671406556917033397649408), (-4129479728217/9671406556917033397649408)), (103837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258275461365639/604462909807314587353088), (-3612001439205/604462909807314587353088)), (45445/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886957331328853/75557863725914323419136), (-5867078124143/75557863725914323419136)), (36939/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296912782019841/4722366482869645213696), (-1099547042845/1180591620717411303424)), (55435/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810292704570173/295147905179352825856), (-1511016121651/147573952589676412928)), (152533/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822394689868209/73786976294838206464), (-7549916748101/73786976294838206464)), (190795/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821439838181403/9223372036854775808), (-8486560118101/9223372036854775808)), (214823/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49771427372281/36028797018963968), (-2119423991211/288230376151711744)), (107523/576460752303423488), by norm_num⟩
  | 5 => ⟨((298360027178881/36028797018963968), (-7408020219971/144115188075855872)), (23/17592186044416), by norm_num⟩
  | 4 => ⟨((744960229850405/18014398509481984), (-11092123888401/36028797018963968)), (283127/36028797018963968), by norm_num⟩
  | 3 => ⟨((371775281729519/2251799813685248), (-6915182981699/4503599627370496)), (177395/4503599627370496), by norm_num⟩
  | 2 => ⟨((277950507692483/562949953421312), (-27556554724291/4503599627370496)), (178057/1125899906842624), by norm_num⟩
  | 1 => ⟨((552377795860143/562949953421312), (-10268763056309/562949953421312)), (1074981/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167246328164519/2251799813685248), (-10139370413501/281474976710656)), (2176627/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2167246328164519/2251799813685248), (-10139370413501/281474976710656)), (8303173073775481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520736455030827/562949953421312), (-156138307961555/2251799813685248)), (271663/140737488355328), by norm_num⟩
  | 2 => ⟨((957963512594709/1125899906842624), (-288860167722801/2251799813685248)), (8644127/2251799813685248), by norm_num⟩
  | 3 => ⟨((796548642457557/1125899906842624), (-491549025341753/2251799813685248)), (8463657/1125899906842624), by norm_num⟩
  | 4 => ⟨((7967024661137/17592186044416), (-347759784380227/1125899906842624)), (7835391/562949953421312), by norm_num⟩
  | 5 => ⟨((247003332347245/2251799813685248), (-1259927911773481/4503599627370496)), (95497203/4503599627370496), by norm_num⟩
  | 6 => ⟨((-149144669736957/2251799813685248), (-276406802091383/4503599627370496)), (148766201/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-672655039/16777216)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-83017565/33554432), (-1384179539/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1391075968196863/18014398509481984), (606359527617409/18014398509481984)), (271343121/18014398509481984), by norm_num⟩
  | 1 => ⟨((437632707/2147483648), (-95380399/1073741824)), (173/4294967296), by norm_num⟩
  | 2 => ⟨((-1154937803/4294967296), (251714341/2147483648)), (115/2147483648), by norm_num⟩
  | 3 => ⟨((507991179/2147483648), (-442859051/4294967296)), (51/1073741824), by norm_num⟩
  | 4 => ⟨((-335154461/2147483648), (146091303/2147483648)), (271/8589934592), by norm_num⟩
  | 5 => ⟨((1415186939/17179869184), (-308434659/8589934592)), (289/17179869184), by norm_num⟩
  | 6 => ⟨((-1244919821/34359738368), (542651165/34359738368)), (1/134217728), by norm_num⟩
  | 7 => ⟨((58668121/4294967296), (-409167867/68719476736)), (195/68719476736), by norm_num⟩
  | 8 => ⟨((-619314139/137438953472), (539908729/274877906944)), (65/68719476736), by norm_num⟩
  | 9 => ⟨((181600613/137438953472), (-316633353/549755813888)), (307/1099511627776), by norm_num⟩
  | 10 => ⟨((-383403543/1099511627776), (83561357/549755813888)), (41/549755813888), by norm_num⟩
  | 11 => ⟨((735871949/8796093022208), (-320761035/8796093022208)), (317/17592186044416), by norm_num⟩
  | 12 => ⟨((-1294672173/70368744177664), (35271115/4398046511104)), (281/70368744177664), by norm_num⟩
  | 13 => ⟨((525648321/140737488355328), (-458252281/281474976710656)), (115/140737488355328), by norm_num⟩
  | 14 => ⟨((-99086861/140737488355328), (172764863/562949953421312)), (175/1125899906842624), by norm_num⟩
  | 15 => ⟨((1115715869/9007199254740992), (-60791517/1125899906842624)), (249/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1472219071/72057594037927936), (320864597/36028797018963968)), (331/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (889205792179/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778143950327327/633825300114114700748351602688), (2103270012333/316912650057057350374175801344)), (92615/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59032455994453/1237940039285380274899124224), (4731320310049/39614081257132168796771975168)), (52109/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944384628351425/1237940039285380274899124224), (5025756864327/2475880078570760549798248448)), (110763/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885217497596695/77371252455336267181195264), (5024327275949/154742504910672534362390528)), (110797/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548844421489319/9671406556917033397649408), (1177197057101/2417851639229258349412352)), (103909/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258167763337061/604462909807314587353088), (4118671494411/604462909807314587353088)), (45479/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943391017341687/37778931862957161709568), (3344997683247/37778931862957161709568)), (36969/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((10131102019161/36893488147419103232), (5015007262879/4722366482869645213696)), (110967/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620403881875999/590295810358705651712), (6891591480019/590295810358705651712)), (76339/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822167170886383/73786976294838206464), (2152106698391/18446744073709551616)), (190995/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821183042559395/9223372036854775808), (9676148521601/9223372036854775808)), (215073/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592427837098925/1152921504606846976), (2416435147083/288230376151711744)), (215327/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596606664980979/72057594037927936), (4222911579533/72057594037927936)), (94349/72057594037927936), by norm_num⟩
  | 4 => ⟨((46549311295999/1125899906842624), (12645357710829/36028797018963968)), (70905/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486668947756075/9007199254740992), (15765838407333/9007199254740992)), (355531/9007199254740992), by norm_num⟩
  | 2 => ⟨((555681904765153/1125899906842624), (7852326258689/1125899906842624)), (178521/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104083302889675/1125899906842624), (11702186047763/562949953421312)), (539351/1125899906842624), by norm_num⟩
  | 0 => ⟨((541109822021335/562949953421312), (23100234129391/562949953421312)), (1093917/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((541109822021335/562949953421312), (23100234129391/562949953421312)), (4172962193015670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038338192924215/1125899906842624), (44408081046775/562949953421312)), (548183/281474976710656), by norm_num⟩
  | 2 => ⟨((950579963397843/1125899906842624), (40954445723909/281474976710656)), (8780701/2251799813685248), by norm_num⟩
  | 3 => ⟨((1557449282111283/2251799813685248), (276617665784417/1125899906842624)), (17381997/2251799813685248), by norm_num⟩
  | 4 => ⟨((235320533531799/562949953421312), (765286474182927/2251799813685248)), (16292707/1125899906842624), by norm_num⟩
  | 5 => ⟨((266763205711585/4503599627370496), (319899877981903/1125899906842624)), (12347733/562949953421312), by norm_num⟩
  | 6 => ⟨((-1391075968196863/18014398509481984), (606359527617409/18014398509481984)), (271343121/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-1384179539/33554432)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-85187893/33554432), (-1420366143/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-57752249863247/9007199254740992), (708871759033601/9007199254740992)), (117920673/9007199254740992), by norm_num⟩
  | 1 => ⟨((149150841/8589934592), (-1830730733/8589934592)), (307/8589934592), by norm_num⟩
  | 2 => ⟨((-100976991/4294967296), (619713841/2147483648)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((45575127/2147483648), (-559405397/2147483648)), (3/67108864), by norm_num⟩
  | 4 => ⟨((-30854933/2147483648), (757448949/4294967296)), (131/4294967296), by norm_num⟩
  | 5 => ⟨((33422683/4294967296), (-1640967823/17179869184)), (143/8589934592), by norm_num⟩
  | 6 => ⟨((-120680405/34359738368), (740637207/17179869184)), (65/8589934592), by norm_num⟩
  | 7 => ⟨((23343471/17179869184), (-1146104421/68719476736)), (203/68719476736), by norm_num⟩
  | 8 => ⟨((-126430583/274877906944), (775927077/137438953472)), (277/274877906944), by norm_num⟩
  | 9 => ⟨((152169051/1099511627776), (-1867777313/1099511627776)), (21/68719476736), by norm_num⟩
  | 10 => ⟨((-41208143/1099511627776), (1011606945/2199023255552)), (23/274877906944), by norm_num⟩
  | 11 => ⟨((81159069/8796093022208), (-996175415/8796093022208)), (183/8796093022208), by norm_num⟩
  | 12 => ⟨((-146521889/70368744177664), (899231011/35184372088832)), (333/70368744177664), by norm_num⟩
  | 13 => ⟨((61044405/140737488355328), (-749280837/140737488355328)), (35/35184372088832), by norm_num⟩
  | 14 => ⟨((-11807951/140737488355328), (1159480069/1125899906842624)), (219/1125899906842624), by norm_num⟩
  | 15 => ⟨((136433169/9007199254740992), (-837314729/4503599627370496)), (319/9007199254740992), by norm_num⟩
  | 16 => ⟨((-11545871/4503599627370496), (141718145/4503599627370496)), (109/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (2152028357547/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889025161782913/316912650057057350374175801344), (636215663155/158456325028528675187087900672)), (92451/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944466809415943/19807040628566084398385987584), (2862337628599/39614081257132168796771975168)), (104023/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888658194340267/2475880078570760549798248448), (3040445925249/2475880078570760549798248448)), (110543/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770324462712185/154742504910672534362390528), (1519779990865/77371252455336267181195264)), (110565/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12099541874051/75557863725914323419136), (1424323241125/4835703278458516698824704)), (103677/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629039073279181/302231454903657293676544), (2491625024973/604462909807314587353088)), (22685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943318730218505/37778931862957161709568), (505890962957/9444732965739290427392)), (73747/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296673548183945/4722366482869645213696), (3033803936957/4722366482869645213696)), (110657/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620257549104893/590295810358705651712), (4168976329347/590295810358705651712)), (38053/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113874155781167/4611686018427387904), (2603733373633/36893488147419103232)), (190355/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455245712712795/2305843009213693952), (2926621399873/4611686018427387904)), (214273/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592231476962435/1152921504606846976), (2923401089223/576460752303423488)), (107213/576460752303423488), by norm_num⟩
  | 5 => ⟨((298261453670603/36028797018963968), (5108714439999/144115188075855872)), (187797/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489335261576553/36028797018963968), (3824308644877/18014398509481984)), (141021/18014398509481984), by norm_num⟩
  | 3 => ⟨((743190257906343/4503599627370496), (9535522673839/9007199254740992)), (176581/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222195345035995/4503599627370496), (18995483096017/4503599627370496)), (354077/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207478835659619/2251799813685248), (14152481875333/1125899906842624)), (1066823/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081750664398749/1125899906842624), (27930371231535/1125899906842624)), (67253/70368744177664), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1081750664398749/1125899906842624), (27930371231535/1125899906842624)), (256549835473513581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2077279493821755/2251799813685248), (53670308440375/1125899906842624)), (2121095/1125899906842624), by norm_num⟩
  | 2 => ⟨((1911168151478305/2251799813685248), (198042881916435/2251799813685248)), (2057815/562949953421312), by norm_num⟩
  | 3 => ⟨((1604646513507661/2251799813685248), (336169535360459/2251799813685248)), (15420079/2251799813685248), by norm_num⟩
  | 4 => ⟨((546647277845441/1125899906842624), (59889123978213/281474976710656)), (13290497/1125899906842624), by norm_num⟩
  | 5 => ⟨((428876368448859/2251799813685248), (930476363556587/4503599627370496)), (74244889/4503599627370496), by norm_num⟩
  | 6 => ⟨((-57752249863247/9007199254740992), (708871759033601/9007199254740992)), (117920673/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-1420366143/33554432)), (1/16777216), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile003Terms1

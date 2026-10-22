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
namespace Reinmann.XiBand97.Tile024Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5865/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5865/256))
  have he : value ((69/80), (5865/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-844544223/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((337542628071017/2251799813685248), (-49556241495449/4503599627370496)), (89293823/9007199254740992), by norm_num⟩
  | 1 => ⟨((-707299193/2147483648), (103841965/4294967296)), (3/134217728), by norm_num⟩
  | 2 => ⟨((1554095171/4294967296), (-114082059/4294967296)), (27/1073741824), by norm_num⟩
  | 3 => ⟨((-1138232035/4294967296), (83554635/4294967296)), (81/4294967296), by norm_num⟩
  | 4 => ⟨((1250475701/8589934592), (-91794149/8589934592)), (91/8589934592), by norm_num⟩
  | 5 => ⟨((-549515189/8589934592), (5042309/1073741824)), (41/8589934592), by norm_num⟩
  | 6 => ⟨((804938853/34359738368), (-118176909/68719476736)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-252661633/34359738368), (74188917/137438953472)), (79/137438953472), by norm_num⟩
  | 8 => ⟨((277577175/137438953472), (-10188107/68719476736)), (89/549755813888), by norm_num⟩
  | 9 => ⟨((-67766599/137438953472), (79593099/2199023255552)), (89/2199023255552), by norm_num⟩
  | 10 => ⟨((238237499/2199023255552), (-139907131/17592186044416)), (159/17592186044416), by norm_num⟩
  | 11 => ⟨((-1522796475/70368744177664), (13973063/8796093022208)), (65/35184372088832), by norm_num⟩
  | 12 => ⟨((557654307/140737488355328), (-81871887/281474976710656)), (97/281474976710656), by norm_num⟩
  | 13 => ⟨((-188506423/281474976710656), (55351053/1125899906842624)), (133/2251799813685248), by norm_num⟩
  | 14 => ⟨((1893444323/18014398509481984), (-138992793/18014398509481984)), (85/9007199254740992), by norm_num⟩
  | 15 => ⟨((-277354827/18014398509481984), (5089973/4503599627370496)), (51/36028797018963968), by norm_num⟩
  | 16 => ⟨((1218821685/576460752303423488), (-44735255/288230376151711744)), (57/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-23862527061/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779045852202447/633825300114114700748351602688), (-56496853243/316912650057057350374175801344)), (23053/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59064173884249/1237940039285380274899124224), (-127096819007/39614081257132168796771975168)), (103739/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889848122463491/2475880078570760549798248448), (-135014269047/2475880078570760549798248448)), (110223/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885757187486809/77371252455336267181195264), (-134984915185/154742504910672534362390528)), (6889/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774928442821811/4835703278458516698824704), (-126517178541/9671406556917033397649408)), (12917/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314763553619983/151115727451828646838272), (-110671361943/604462909807314587353088)), (22605/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944111769200401/37778931862957161709568), (-89891271173/37778931862957161709568)), (146935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297863077996103/4722366482869645213696), (-134785810131/4722366482869645213696)), (110203/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621893105455519/590295810358705651712), (-92623748677/295147905179352825856)), (151531/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824030866233615/73786976294838206464), (-115717477533/36893488147419103232)), (94709/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823282671101959/9223372036854775808), (-260193366463/9223372036854775808)), (213101/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594531169553031/1152921504606846976), (-259979841163/1152921504606846976)), (213109/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149382237347071/18014398509481984), (-227242381593/144115188075855872)), (93239/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492353085632219/36028797018963968), (-85096051063/9007199254740992)), (139867/18014398509481984), by norm_num⟩
  | 3 => ⟨((745076124375981/4503599627370496), (-424642688431/9007199254740992)), (349697/9007199254740992), by norm_num⟩
  | 2 => ⟨((278717136987715/562949953421312), (-846777976923/4503599627370496)), (699483/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218786918097309/2251799813685248), (-1263916978899/2251799813685248)), (524727/1125899906842624), by norm_num⟩
  | 0 => ⟨((546524447750591/562949953421312), (-1251472389789/1125899906842624)), (1049931/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546524447750591/562949953421312), (-1251472389789/1125899906842624)), (4005168919089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((530577502721213/562949953421312), (-1214957479875/562949953421312)), (4081855/2251799813685248), by norm_num⟩
  | 2 => ⟨((2000256033853993/2251799813685248), (-2290182641163/562949953421312)), (1927969/562949953421312), by norm_num⟩
  | 3 => ⟨((1776774408483929/2251799813685248), (-16274809576849/2251799813685248)), (13763545/2251799813685248), by norm_num⟩
  | 4 => ⟨((1401839723954203/2251799813685248), (-12841578982001/1125899906842624)), (10959551/1125899906842624), by norm_num⟩
  | 5 => ⟨((1744822053109545/4503599627370496), (-63955367349651/4503599627370496)), (27791121/2251799813685248), by norm_num⟩
  | 6 => ⟨((337542628071017/2251799813685248), (-49556241495449/4503599627370496)), (89293823/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-844544223/16777216)), (1/16777216), by norm_num⟩, -8, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-885041501/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-980751470967557/9007199254740992), (-188136293029225/2251799813685248)), (336289569/9007199254740992), by norm_num⟩
  | 1 => ⟨((1076824053/4294967296), (206565773/1073741824)), (93/1073741824), by norm_num⟩
  | 2 => ⟨((-619869753/2147483648), (-237817635/1073741824)), (27/268435456), by norm_num⟩
  | 3 => ⟨((951535235/4294967296), (365063561/2147483648)), (167/2147483648), by norm_num⟩
  | 4 => ⟨((-4279279/33554432), (-420294957/4294967296)), (387/8589934592), by norm_num⟩
  | 5 => ⟨((1008988573/17179869184), (387105961/8589934592)), (359/17179869184), by norm_num⟩
  | 6 => ⟨((-774427349/34359738368), (-297114805/17179869184)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((1018962783/137438953472), (781865281/137438953472)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((-1173124257/549755813888), (-900155671/549755813888)), (427/549755813888), by norm_num⟩
  | 9 => ⟨((1200541523/2199023255552), (921193347/2199023255552)), (55/274877906944), by norm_num⟩
  | 10 => ⟨((-552869803/4398046511104), (-212112607/2199023255552)), (51/1099511627776), by norm_num⟩
  | 11 => ⟨((462919915/17592186044416), (710410657/35184372088832)), (43/4398046511104), by norm_num⟩
  | 12 => ⟨((-355304165/70368744177664), (-272630165/70368744177664)), (133/70368744177664), by norm_num⟩
  | 13 => ⟨((1006914553/1125899906842624), (772620497/1125899906842624)), (379/1125899906842624), by norm_num⟩
  | 14 => ⟨((-662430411/4503599627370496), (-508292697/4503599627370496)), (251/4503599627370496), by norm_num⟩
  | 15 => ⟨((50843413/2251799813685248), (156051625/9007199254740992)), (155/18014398509481984), by norm_num⟩
  | 16 => ⟨((-936570279/288230376151711744), (-718644291/288230376151711744)), (359/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-3239727808405/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444724467819553/158456325028528675187087900672), (-3834610300825/633825300114114700748351602688)), (69433/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889886666899671/39614081257132168796771975168), (-4313168630157/39614081257132168796771975168)), (39065/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236208781151475/309485009821345068724781056), (-4581811236227/2475880078570760549798248448)), (166069/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771335889325127/154742504910672534362390528), (-4580764584299/154742504910672534362390528)), (166117/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549688905086027/9671406556917033397649408), (-4293354893529/9671406556917033397649408)), (19473/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258906581690471/604462909807314587353088), (-3755573811149/604462909807314587353088)), (68181/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887982417718265/75557863725914323419136), (-6100723357083/75557863725914323419136)), (110841/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297681173237265/4722366482869645213696), (-4573719332993/4722366482869645213696)), (166345/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810820629421555/295147905179352825856), (-6285902140083/590295810358705651712)), (228857/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455928367454733/18446744073709551616), (-7852936043761/73786976294838206464)), (143137/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822922046633413/9223372036854775808), (-8828447892361/9223372036854775808)), (10073/288230376151711744), by norm_num⟩
  | 6 => ⟨((398541527751157/288230376151711744), (-8820819578451/1152921504606846976)), (322683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597366747458699/72057594037927936), (-7709639589341/144115188075855872)), (282739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491856551327297/36028797018963968), (-11547315092533/36028797018963968)), (212445/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489514266045061/9007199254740992), (-7202082837795/4503599627370496)), (532483/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114204712928023/2251799813685248), (-14359247124411/2251799813685248)), (534543/2251799813685248), by norm_num⟩
  | 1 => ⟨((277083373602217/281474976710656), (-10713372648931/562949953421312)), (403487/562949953421312), by norm_num⟩
  | 0 => ⟨((1090674621551685/1125899906842624), (-42406018317675/1125899906842624)), (1634659/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090674621551685/1125899906842624), (-42406018317675/1125899906842624)), (6235729221824264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054954221497575/1125899906842624), (-82158578571779/1125899906842624)), (1645085/562949953421312), by norm_num⟩
  | 2 => ⟨((982483763165671/1125899906842624), (-9622695895277/70368744177664)), (6645875/1125899906842624), by norm_num⟩
  | 3 => ⟨((836281886543211/1125899906842624), (-537405780675647/2251799813685248)), (26832525/2251799813685248), by norm_num⟩
  | 4 => ⟨((139258860106655/281474976710656), (-798335122636219/2251799813685248)), (26334075/1125899906842624), by norm_num⟩
  | 5 => ⟨((536295416547119/4503599627370496), (-394973792912717/1125899906842624)), (178919791/4503599627370496), by norm_num⟩
  | 6 => ⟨((-980751470967557/9007199254740992), (-188136293029225/2251799813685248)), (336289569/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-885041501/16777216)), (3/33554432), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-921675745/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-23743016092717/4503599627370496), (71103438026945/562949953421312)), (185358587/9007199254740992), by norm_num⟩
  | 1 => ⟨((27147897/2147483648), (-1300801071/4294967296)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((-32548907/2147483648), (779796185/2147483648)), (259/4294967296), by norm_num⟩
  | 3 => ⟨((13008145/1073741824), (-311644931/1073741824)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((-62384339/8589934592), (747291907/4294967296)), (253/8589934592), by norm_num⟩
  | 5 => ⟨((59836445/17179869184), (-1433542185/17179869184)), (245/17179869184), by norm_num⟩
  | 6 => ⟨((-5978397/4294967296), (572914005/17179869184)), (99/17179869184), by norm_num⟩
  | 7 => ⟨((32767017/68719476736), (-785021591/68719476736)), (273/137438953472), by norm_num⟩
  | 8 => ⟨((-78571875/549755813888), (941199781/274877906944)), (165/274877906944), by norm_num⟩
  | 9 => ⟨((83736501/2199023255552), (-2006132005/2199023255552)), (177/1099511627776), by norm_num⟩
  | 10 => ⟨((-627473/68719476736), (1924197781/8796093022208)), (171/4398046511104), by norm_num⟩
  | 11 => ⟨((8754121/4398046511104), (-1677827187/35184372088832)), (301/35184372088832), by norm_num⟩
  | 12 => ⟨((-55977241/140737488355328), (1341084627/140737488355328)), (121/70368744177664), by norm_num⟩
  | 13 => ⟨((10325197/140737488355328), (-989470919/562949953421312)), (45/140737488355328), by norm_num⟩
  | 14 => ⟨((-3536963/281474976710656), (1355798651/4503599627370496)), (31/562949953421312), by norm_num⟩
  | 15 => ⟨((72373477/36028797018963968), (-1733900361/36028797018963968)), (5/562949953421312), by norm_num⟩
  | 16 => ⟨((-43386005/144115188075855872), (519713935/72057594037927936)), (97/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (2100477420445/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778775697294539/633825300114114700748351602688), (1242916109787/316912650057057350374175801344)), (92445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236218688216125/4951760157141521099596496896), (2796051448579/39614081257132168796771975168)), (104017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472381220533289/618970019642690137449562112), (742544368479/618970019642690137449562112)), (110535/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885595467238035/77371252455336267181195264), (2969472070491/154742504910672534362390528)), (27639/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549553447659885/9671406556917033397649408), (1391565382241/4835703278458516698824704)), (25917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629394246953685/302231454903657293676544), (2434490330483/604462909807314587353088)), (90731/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887791344722227/75557863725914323419136), (3954642699093/75557863725914323419136)), (147479/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324384646272649/1180591620717411303424), (1482376950071/2361183241434822606848)), (110645/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810723181751233/295147905179352825856), (4074541759631/590295810358705651712)), (152195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823471593735223/73786976294838206464), (5090186404755/73786976294838206464)), (95165/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822652329624959/9223372036854775808), (5722349774491/9223372036854775808)), (107121/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593899381232833/1152921504606846976), (2858607988693/576460752303423488)), (26799/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194503460488775/144115188075855872), (624599178587/18014398509481984)), (93881/72057594037927936), by norm_num⟩
  | 4 => ⟨((745759095822699/18014398509481984), (7483661458317/36028797018963968)), (281981/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489102990784591/9007199254740992), (9334429545855/9007199254740992)), (353069/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227621752228319/4503599627370496), (18608528845651/4503599627370496)), (353959/2251799813685248), by norm_num⟩
  | 1 => ⟨((2215572160168089/2251799813685248), (27762357751409/2251799813685248)), (266585/562949953421312), by norm_num⟩
  | 0 => ⟨((2179503258512435/2251799813685248), (54925310423283/2251799813685248)), (2150595/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179503258512435/2251799813685248), (54925310423283/2251799813685248)), (8203868874556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1054094070727369/1125899906842624), (106323743624827/2251799813685248)), (2134005/1125899906842624), by norm_num⟩
  | 2 => ⟨((492178797863117/562949953421312), (49771399327477/562949953421312)), (524667/140737488355328), by norm_num⟩
  | 3 => ⟨((1703616994141781/2251799813685248), (348115172087131/2251799813685248)), (16163051/2251799813685248), by norm_num⟩
  | 4 => ⟨((1235068354117985/2251799813685248), (65842323047763/281474976710656)), (29453997/2251799813685248), by norm_num⟩
  | 5 => ⟨((554196823129003/2251799813685248), (288905857665275/1125899906842624)), (2880599/140737488355328), by norm_num⟩
  | 6 => ⟨((-23743016092717/4503599627370496), (71103438026945/562949953421312)), (185358587/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-921675745/16777216)), (1/16777216), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1910240379/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((980602491240191/9007199254740992), (-392725051949363/9007199254740992)), (136824775/9007199254740992), by norm_num⟩
  | 1 => ⟨((-580955899/2147483648), (232669137/2147483648)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((180452647/536870912), (-289080543/2147483648)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((-298938655/1073741824), (478892109/4294967296)), (87/2147483648), by norm_num⟩
  | 4 => ⟨((1485669303/8589934592), (-595001093/8589934592)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-369174953/4294967296), (591408869/17179869184)), (219/17179869184), by norm_num⟩
  | 6 => ⟨((1223153727/34359738368), (-489865277/34359738368)), (183/34359738368), by norm_num⟩
  | 7 => ⟨((-868406523/68719476736), (347791281/68719476736)), (33/17179869184), by norm_num⟩
  | 8 => ⟨((269738643/68719476736), (-432114433/274877906944)), (83/137438953472), by norm_num⟩
  | 9 => ⟨((-595800309/549755813888), (477228457/1099511627776)), (185/1099511627776), by norm_num⟩
  | 10 => ⟨((148050815/549755813888), (-237173633/2199023255552)), (93/2199023255552), by norm_num⟩
  | 11 => ⟨((-1070232595/17592186044416), (53577667/2199023255552)), (85/8796093022208), by norm_num⟩
  | 12 => ⟨((886476031/70368744177664), (-355028003/70368744177664)), (143/70368744177664), by norm_num⟩
  | 13 => ⟨((-677787749/281474976710656), (542899351/562949953421312)), (221/562949953421312), by norm_num⟩
  | 14 => ⟨((60151403/140737488355328), (-385444059/2251799813685248)), (159/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1275482635/18014398509481984), (510822669/18014398509481984)), (213/18014398509481984), by norm_num⟩
  | 16 => ⟨((198090955/18014398509481984), (-158668331/36028797018963968)), (67/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-248103131859/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444665783844057/158456325028528675187087900672), (-587167818757/633825300114114700748351602688)), (138387/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889623073768099/39614081257132168796771975168), (-660440428587/39614081257132168796771975168)), (155691/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236173850920083/309485009821345068724781056), (-175391145775/618970019642690137449562112)), (41357/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221382143882941/19342813113834066795298816), (-175348026567/38685626227668133590597632)), (41359/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774714167547853/4835703278458516698824704), (-328685951203/4835703278458516698824704)), (4847/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258679329590749/604462909807314587353088), (-35938580265/37778931862957161709568)), (33931/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235951816496601/9444732965739290427392), (-934059859463/75557863725914323419136)), (220565/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297406481943913/4722366482869645213696), (-350122356269/2361183241434822606848)), (41359/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621265543773409/590295810358705651712), (-481174474943/295147905179352825856)), (28437/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911623400386821/36893488147419103232), (-601102678885/36893488147419103232)), (284401/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822401128781621/9223372036854775808), (-84467305763/576460752303423488)), (159997/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593650290918343/1152921504606846976), (-675111427625/576460752303423488)), (20003/72057594037927936), by norm_num⟩
  | 5 => ⟨((298571968993973/36028797018963968), (-295008940481/36028797018963968)), (140051/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491199541837743/36028797018963968), (-1767239053311/36028797018963968)), (420275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488712923617795/9007199254740992), (-275516501191/1125899906842624)), (525557/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226866245069175/4503599627370496), (-4393548432855/4503599627370496)), (525879/2251799813685248), by norm_num⟩
  | 1 => ⟨((553625022538791/562949953421312), (-3276827660887/1125899906842624)), (1579259/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088800813666211/1125899906842624), (-12961368886831/2251799813685248)), (3165063/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088800813666211/1125899906842624), (-12961368886831/2251799813685248)), (12073757180220793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105773711081845/2251799813685248), (-12534283824381/1125899906842624)), (6157981/2251799813685248), by norm_num⟩
  | 2 => ⟨((1968938118856765/2251799813685248), (-2930363214817/140737488355328)), (45525/8796093022208), by norm_num⟩
  | 3 => ⟨((215079012187597/281474976710656), (-81992422959571/2251799813685248)), (20866171/2251799813685248), by norm_num⟩
  | 4 => ⟨((1311773826241209/2251799813685248), (-62651570463189/1125899906842624)), (16703915/1125899906842624), by norm_num⟩
  | 5 => ⟨((1514388342803029/4503599627370496), (-145989336719975/2251799813685248)), (5330139/281474976710656), by norm_num⟩
  | 6 => ⟨((980602491240191/9007199254740992), (-392725051949363/9007199254740992)), (136824775/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1910240379/33554432)), (3/33554432), by norm_num⟩, -9, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1971772193/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-73981152783185/1125899906842624), (-394216686214161/4503599627370496)), (33513381/1125899906842624), by norm_num⟩
  | 1 => ⟨((361934491/2147483648), (482151907/2147483648)), (165/2147483648), by norm_num⟩
  | 2 => ⟨((-116042955/536870912), (-154586903/536870912)), (213/2147483648), by norm_num⟩
  | 3 => ⟨((793718141/4294967296), (264338385/1073741824)), (183/2147483648), by norm_num⟩
  | 4 => ⟨((-508961709/4294967296), (-678014571/4294967296)), (59/1073741824), by norm_num⟩
  | 5 => ⟨((522184403/8589934592), (695629215/8589934592)), (61/2147483648), by norm_num⟩
  | 6 => ⟨((-892917699/34359738368), (-148687809/4294967296)), (105/8589934592), by norm_num⟩
  | 7 => ⟨((327184097/34359738368), (217929543/17179869184)), (155/34359738368), by norm_num⟩
  | 8 => ⟨((-52450665/17179869184), (-1117956483/274877906944)), (25/17179869184), by norm_num⟩
  | 9 => ⟨((119585155/137438953472), (318611307/274877906944)), (115/274877906944), by norm_num⟩
  | 10 => ⟨((-245383893/1099511627776), (-326888747/1099511627776)), (119/1099511627776), by norm_num⟩
  | 11 => ⟨((457743461/8796093022208), (1219568119/17592186044416)), (223/8796093022208), by norm_num⟩
  | 12 => ⟨((-97840733/8796093022208), (-1042710155/70368744177664)), (3/549755813888), by norm_num⟩
  | 13 => ⟨((617739139/281474976710656), (411461345/140737488355328)), (305/281474976710656), by norm_num⟩
  | 14 => ⟨((-905411205/2251799813685248), (-1206145729/2251799813685248)), (225/1125899906842624), by norm_num⟩
  | 15 => ⟨((619289037/9007199254740992), (412493695/4503599627370496)), (155/4503599627370496), by norm_num⟩
  | 16 => ⟨((-794222509/72057594037927936), (-529012719/36028797018963968)), (25/4503599627370496), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-2884923730243/10141204801825835211973625643008)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889275336590901/316912650057057350374175801344), (-853345410715/158456325028528675187087900672)), (34701/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236187029666397/4951760157141521099596496896), (-3839302168143/39614081257132168796771975168)), (156187/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236156953407947/309485009821345068724781056), (-4078336758449/2475880078570760549798248448)), (82993/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770921502962045/154742504910672534362390528), (-2038649974255/77371252455336267181195264)), (41507/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549300668095549/9671406556917033397649408), (-238835458809/604462909807314587353088)), (155697/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258567124454029/604462909807314587353088), (-52228052239/9444732965739290427392)), (17035/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943715634250997/37778931862957161709568), (-2714826752201/37778931862957161709568)), (110769/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297268221317655/4722366482869645213696), (-4070434787503/4722366482869645213696)), (166227/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405268528953565/147573952589676412928), (-1398478818159/147573952589676412928)), (114341/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227875692395421/9223372036854775808), (-3493998604047/36893488147419103232)), (17877/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911063498001023/4611686018427387904), (-7855454326417/9223372036854775808)), (322033/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593372772958309/1152921504606846976), (-7847905932043/1152921504606846976)), (161171/576460752303423488), by norm_num⟩
  | 5 => ⟨((597020624285409/72057594037927936), (-3429216153789/72057594037927936)), (141199/72057594037927936), by norm_num⟩
  | 4 => ⟨((93176376572429/2251799813685248), (-10270694096937/36028797018963968)), (212147/18014398509481984), by norm_num⟩
  | 3 => ⟨((93014238858757/562949953421312), (-12808734385905/9007199254740992)), (531589/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112928313806825/2251799813685248), (-797772395971/140737488355328)), (33339/140737488355328), by norm_num⟩
  | 1 => ⟨((2212887842850183/2251799813685248), (-19035855673837/1125899906842624)), (804737/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173990109232581/2251799813685248), (-75261067390117/2251799813685248)), (1627943/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2173990109232581/2251799813685248), (-75261067390117/2251799813685248)), (6210109714988326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096353653680611/2251799813685248), (-145320925174631/2251799813685248)), (6504403/2251799813685248), by norm_num⟩
  | 2 => ⟨((242782486892603/281474976710656), (-270578273072605/2251799813685248)), (12950313/2251799813685248), by norm_num⟩
  | 3 => ⟨((1642757440484695/2251799813685248), (-466767361016259/2251799813685248)), (25452483/2251799813685248), by norm_num⟩
  | 4 => ⟨((550843868065197/1125899906842624), (-681042382741795/2251799813685248)), (47688649/2251799813685248), by norm_num⟩
  | 5 => ⟨((666042457497343/4503599627370496), (-1332793503741771/4503599627370496)), (37754685/1125899906842624), by norm_num⟩
  | 6 => ⟨((-73981152783185/1125899906842624), (-394216686214161/4503599627370496)), (33513381/1125899906842624), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1971772193/33554432)), (3/33554432), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-2028741753/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-663318404244015/9007199254740992), (644429526388875/9007199254740992)), (42201177/2251799813685248), by norm_num⟩
  | 1 => ⟨((208680069/1073741824), (-810950501/4294967296)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((-550718665/2147483648), (66879527/268435456)), (143/2147483648), by norm_num⟩
  | 3 => ⟨((968918753/4294967296), (-470663749/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-319629017/2147483648), (155263577/1073741824)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((42175965/536870912), (-655599169/8589934592)), (45/2147483648), by norm_num⟩
  | 6 => ⟨((-74203193/2147483648), (36045079/1073741824)), (5/536870912), by norm_num⟩
  | 7 => ⟨((895206767/68719476736), (-869714559/68719476736)), (243/68719476736), by norm_num⟩
  | 8 => ⟨((-590625495/137438953472), (573806645/137438953472)), (81/68719476736), by norm_num⟩
  | 9 => ⟨((692753129/549755813888), (-673026059/549755813888)), (3/8589934592), by norm_num⟩
  | 10 => ⟨((-731286089/2199023255552), (710461741/2199023255552)), (205/2199023255552), by norm_num⟩
  | 11 => ⟨((21930749/274877906944), (-681799733/8796093022208)), (199/8796093022208), by norm_num⟩
  | 12 => ⟨((-617349375/35184372088832), (599769527/35184372088832)), (177/35184372088832), by norm_num⟩
  | 13 => ⟨((1002597165/281474976710656), (-974046871/281474976710656)), (145/140737488355328), by norm_num⟩
  | 14 => ⟨((-755974685/1125899906842624), (734447295/1125899906842624)), (221/1125899906842624), by norm_num⟩
  | 15 => ⟨((266008071/2251799813685248), (-516866271/4503599627370496)), (313/9007199254740992), by norm_num⟩
  | 16 => ⟨((-702010549/36028797018963968), (170504965/9007199254740992)), (209/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (3088019776065/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778451256872505/633825300114114700748351602688), (1826647571829/316912650057057350374175801344)), (5785/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889384365985813/39614081257132168796771975168), (4109128238699/39614081257132168796771975168)), (104153/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889136724277359/2475880078570760549798248448), (4364933517765/2475880078570760549798248448)), (110689/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885401277702021/77371252455336267181195264), (4363791594611/154742504910672534362390528)), (865/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((1549189107457767/9671406556917033397649408), (2044920799135/4835703278458516698824704)), (12979/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314617365414025/151115727451828646838272), (1788699341057/302231454903657293676544)), (90885/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887272478012881/75557863725914323419136), (2905499832027/37778931862957161709568)), (36937/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297149051195829/4722366482869645213696), (4356261351813/4722366482869645213696)), (6929/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810455065802509/295147905179352825856), (748328678945/73786976294838206464)), (76261/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113925023212323/4611686018427387904), (3739222014025/36893488147419103232)), (190781/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910947962574479/4611686018427387904), (8406594195175/9223372036854775808)), (214805/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398285345440729/288230376151711744), (8398280216053/1152921504606846976)), (215025/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193838422335243/144115188075855872), (1834787275379/36028797018963968)), (47099/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490517071533519/36028797018963968), (5495024663615/18014398509481984)), (70773/9007199254740992), by norm_num⟩
  | 3 => ⟨((743922693915453/4503599627370496), (13704921759681/9007199254740992)), (22171/562949953421312), by norm_num⟩
  | 2 => ⟨((556272016616851/1125899906842624), (3414010566637/562949953421312)), (356047/2251799813685248), by norm_num⟩
  | 1 => ⟨((69116433764925/70368744177664), (5090536496743/281474976710656)), (537355/1125899906842624), by norm_num⟩
  | 0 => ⟨((542907593668837/562949953421312), (20119155408567/562949953421312)), (1087895/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((542907593668837/562949953421312), (20119155408567/562949953421312)), (4149990086082076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045719510446947/1125899906842624), (19402865535615/281474976710656)), (4352175/2251799813685248), by norm_num⟩
  | 2 => ⟨((1931798286622509/2251799813685248), (36042200422719/281474976710656)), (8684491/2251799813685248), by norm_num⟩
  | 3 => ⟨((810175492621241/1125899906842624), (247362169939129/1125899906842624)), (17124747/2251799813685248), by norm_num⟩
  | 4 => ⟨((1057280992936917/2251799813685248), (355993932796915/1125899906842624)), (16084969/1125899906842624), by norm_num⟩
  | 5 => ⟨((542602742535095/4503599627370496), (1337190336226401/4503599627370496)), (101105383/4503599627370496), by norm_num⟩
  | 6 => ⟨((-663318404244015/9007199254740992), (644429526388875/9007199254740992)), (42201177/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-2028741753/33554432)), (1/16777216), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1040889573/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((613321742613179/9007199254740992), (309496236420503/4503599627370496)), (99791545/4503599627370496), by norm_num⟩
  | 1 => ⟨((-395990865/2147483648), (-399652169/2147483648)), (65/1073741824), by norm_num⟩
  | 2 => ⟨((536181571/2147483648), (135284767/536870912)), (89/1073741824), by norm_num⟩
  | 3 => ⟨((-968004407/4294967296), (-244238627/1073741824)), (81/1073741824), by norm_num⟩
  | 4 => ⟨((163837783/1073741824), (661410463/4294967296)), (221/4294967296), by norm_num⟩
  | 5 => ⟨((-354944753/4294967296), (-716453095/8589934592)), (241/8589934592), by norm_num⟩
  | 6 => ⟨((640805473/17179869184), (161682579/4294967296)), (219/17179869184), by norm_num⟩
  | 7 => ⟨((-123952385/8589934592), (-1000787521/68719476736)), (341/68719476736), by norm_num⟩
  | 8 => ⟨((335669281/68719476736), (42346607/8589934592)), (233/137438953472), by norm_num⟩
  | 9 => ⟨((-404004117/274877906944), (-815479023/549755813888)), (283/549755813888), by norm_num⟩
  | 10 => ⟨((109406343/274877906944), (883343253/2199023255552)), (309/2199023255552), by norm_num⟩
  | 11 => ⟨((-107737407/1099511627776), (-434934159/4398046511104)), (307/8796093022208), by norm_num⟩
  | 12 => ⟨((778022151/35184372088832), (785215691/35184372088832)), (279/35184372088832), by norm_num⟩
  | 13 => ⟨((-648284013/140737488355328), (-654278003/140737488355328)), (117/70368744177664), by norm_num⟩
  | 14 => ⟨((1003191801/1125899906842624), (253116811/281474976710656)), (91/281474976710656), by norm_num⟩
  | 15 => ⟨((-724451669/4503599627370496), (-182787475/1125899906842624)), (265/4503599627370496), by norm_num⟩
  | 16 => ⟨((61307859/2251799813685248), (989995317/36028797018963968)), (361/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1029062973035/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889182956791757/316912650057057350374175801344), (608658898549/316912650057057350374175801344)), (184639/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944644365189085/19807040628566084398385987584), (171150570733/4951760157141521099596496896)), (207735/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889035603746823/2475880078570760549798248448), (727216660225/1237940039285380274899124224)), (220737/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770701988231115/154742504910672534362390528), (1454043634683/154742504910672534362390528)), (220757/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774547706638297/4835703278458516698824704), (170344001077/1208925819614629174706176)), (206981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157298508292761/75557863725914323419136), (1191994268685/604462909807314587353088)), (90565/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887141310476371/75557863725914323419136), (1936215266211/75557863725914323419136)), (294375/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648525818479125/2361183241434822606848), (1451483296587/4722366482869645213696)), (220817/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810388873771027/295147905179352825856), (997344085399/295147905179352825856)), (303681/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113914826810449/4611686018427387904), (1245854642027/36893488147419103232)), (189843/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821715599113959/9223372036854775808), (1400452362395/4611686018427387904)), (427265/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592965059632217/1152921504606846976), (2798072160063/1152921504606846976)), (427413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596844317217373/72057594037927936), (2445130227181/144115188075855872)), (374153/144115188075855872), by norm_num⟩
  | 4 => ⟨((745150675789795/18014398509481984), (1830669404885/18014398509481984)), (280781/18014398509481984), by norm_num⟩
  | 3 => ⟨((743795681374509/4503599627370496), (4565570464943/9007199254740992)), (351269/4503599627370496), by norm_num⟩
  | 2 => ⟨((139039166100139/281474976710656), (9097915160243/4503599627370496)), (351709/1125899906842624), by norm_num⟩
  | 1 => ⟨((552787389104875/562949953421312), (6782049709565/1125899906842624)), (2114673/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085468009656251/1125899906842624), (26798846585225/2251799813685248)), (4247131/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085468009656251/1125899906842624), (26798846585225/2251799813685248)), (16201519021041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2092657168337781/2251799813685248), (51672960424205/2251799813685248)), (4145159/1125899906842624), by norm_num⟩
  | 2 => ⟨((15184186995797/17592186044416), (24010524910733/562949953421312)), (15789307/2251799813685248), by norm_num⟩
  | 3 => ⟨((836722542808139/1125899906842624), (165791925661239/2251799813685248)), (28603037/2251799813685248), by norm_num⟩
  | 4 => ⟨((1231428955232343/2251799813685248), (123209746064683/1125899906842624)), (23362541/1125899906842624), by norm_num⟩
  | 5 => ⟨((1292916623259655/4503599627370496), (539032103826553/4503599627370496)), (122662043/4503599627370496), by norm_num⟩
  | 6 => ⟨((613321742613179/9007199254740992), (309496236420503/4503599627370496)), (99791545/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1040889573/16777216)), (1/8388608), by norm_num⟩, -10, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile024Terms1

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile059Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨59,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15847/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15847/512))
  have he : value ((69/80), (15847/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1017427393/536870912), (-1140962685/16777216)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((603968695838543/9007199254740992), (605806384941891/4503599627370496)), (5691679/9007199254740992), by norm_num⟩
  | 1 => ⟨((-40498500441/274877906944), (-81243449591/274877906944)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((44492150257/274877906944), (44627526047/137438953472)), (425/274877906944), by norm_num⟩
  | 3 => ⟨((-8146603837/68719476736), (-65371131371/274877906944)), (157/137438953472), by norm_num⟩
  | 4 => ⟨((35799836345/549755813888), (8977191031/68719476736)), (347/549755813888), by norm_num⟩
  | 5 => ⟨((-31464112113/1099511627776), (-15779923815/274877906944)), (307/1099511627776), by norm_num⟩
  | 6 => ⟨((2880571685/274877906944), (46229381913/2199023255552)), (227/2199023255552), by norm_num⟩
  | 7 => ⟨((-28933773271/8796093022208), (-58043619505/8796093022208)), (287/8796093022208), by norm_num⟩
  | 8 => ⟨((31786998873/35184372088832), (63767433667/35184372088832)), (317/35184372088832), by norm_num⟩
  | 9 => ⟨((-1940088199/8796093022208), (-62271721105/140737488355328)), (39/17592186044416), by norm_num⟩
  | 10 => ⟨((27281980627/562949953421312), (27364991217/281474976710656)), (69/140737488355328), by norm_num⟩
  | 11 => ⟨((-10899025155/1125899906842624), (-87457500015/4503599627370496)), (111/1125899906842624), by norm_num⟩
  | 12 => ⟨((31930141253/18014398509481984), (32027294751/9007199254740992)), (327/18014398509481984), by norm_num⟩
  | 13 => ⟨((-43173963765/144115188075855872), (-86610657443/144115188075855872)), (445/144115188075855872), by norm_num⟩
  | 14 => ⟨((13551842041/288230376151711744), (54372304341/576460752303423488)), (141/288230376151711744), by norm_num⟩
  | 15 => ⟨((-31761536427/4611686018427387904), (-31858176913/2305843009213693952)), (333/4611686018427387904), by norm_num⟩
  | 16 => ⟨((17446807113/18446744073709551616), (34999784651/18446744073709551616)), (23/2305843009213693952), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (1443766345295/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111190268519873/39614081257132168796771975168), (854564304091/316912650057057350374175801344)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890051725321691/39614081257132168796771975168), (1922448832245/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889846054127387/2475880078570760549798248448), (2042206883537/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442878044501041/38685626227668133590597632), (255220329127/19342813113834066795298816)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774927344695597/4835703278458516698824704), (956840286811/4835703278458516698824704)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259052156254815/604462909807314587353088), (1673998743599/604462909807314587353088)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888219938029243/75557863725914323419136), (339920462687/9444732965739290427392)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297860154120749/4722366482869645213696), (1019374670641/2361183241434822606848)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621888722137531/590295810358705651712), (2802024056021/590295810358705651712)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912012421611617/36893488147419103232), (437580823521/9223372036854775808)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823275148412267/9223372036854775808), (3935639167957/9223372036854775808)), (1671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594522714870649/1152921504606846976), (3932406177719/1152921504606846976)), (6687/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597524727256401/72057594037927936), (1718610735849/72057594037927936)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((746169165791517/18014398509481984), (5148572284101/36028797018963968)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490130164429699/9007199254740992), (1605757086491/2251799813685248)), (1375/1125899906842624), by norm_num⟩
  | 2 => ⟨((2229682048398081/4503599627370496), (6404033502237/2251799813685248)), (22037/4503599627370496), by norm_num⟩
  | 1 => ⟨((277334663961075/281474976710656), (4779343896257/562949953421312)), (33151/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185771405654249/2251799813685248), (2366084007695/140737488355328)), (66685/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185771405654249/2251799813685248), (2366084007695/140737488355328)), (254383095748137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2121042656742709/2251799813685248), (36747272015671/1125899906842624)), (131703/2251799813685248), by norm_num⟩
  | 2 => ⟨((997739780510497/1125899906842624), (34613437211635/562949953421312)), (64177/562949953421312), by norm_num⟩
  | 3 => ⟨((879911529834771/1125899906842624), (61346844486555/562949953421312)), (486543/2251799813685248), by norm_num⟩
  | 4 => ⟨((337148335481857/562949953421312), (383549517712115/2251799813685248)), (866527/2251799813685248), by norm_num⟩
  | 5 => ⟨((371168378111307/1125899906842624), (57426544173959/281474976710656)), (1333111/2251799813685248), by norm_num⟩
  | 6 => ⟨((603968695838543/9007199254740992), (605806384941891/4503599627370496)), (5691679/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-1140962685/16777216)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-38261558837/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-679403601639827/9007199254740992), (-129095921298995/1125899906842624)), (217053/281474976710656), by norm_num⟩
  | 1 => ⟨((1491913419/8589934592), (72571861315/274877906944)), (491/274877906944), by norm_num⟩
  | 2 => ⟨((-27482060789/137438953472), (-41775721509/137438953472)), (285/137438953472), by norm_num⟩
  | 3 => ⟨((42186522331/274877906944), (64128102397/274877906944)), (55/34359738368), by norm_num⟩
  | 4 => ⟨((-24284514361/274877906944), (-36915103155/274877906944)), (509/549755813888), by norm_num⟩
  | 5 => ⟨((22366864303/549755813888), (68000132985/1099511627776)), (59/137438953472), by norm_num⟩
  | 6 => ⟨((-34334405547/2199023255552), (-13048007711/549755813888)), (91/549755813888), by norm_num⟩
  | 7 => ⟨((45175937365/8796093022208), (68672338397/8796093022208)), (481/8796093022208), by norm_num⟩
  | 8 => ⟨((-52010719969/35184372088832), (-79061951347/35184372088832)), (139/8796093022208), by norm_num⟩
  | 9 => ⟨((26613135217/70368744177664), (10113715033/17592186044416)), (571/140737488355328), by norm_num⟩
  | 10 => ⟨((-49023206743/562949953421312), (-74520606303/562949953421312)), (33/35184372088832), by norm_num⟩
  | 11 => ⟨((20523655465/1125899906842624), (62396377161/2251799813685248)), (111/562949953421312), by norm_num⟩
  | 12 => ⟨((-15752487709/4503599627370496), (-23945494651/4503599627370496)), (343/9007199254740992), by norm_num⟩
  | 13 => ⟨((44641776463/72057594037927936), (33930177863/36028797018963968)), (61/9007199254740992), by norm_num⟩
  | 14 => ⟨((-29368996859/288230376151711744), (-44644069571/288230376151711744)), (323/288230376151711744), by norm_num⟩
  | 15 => ⟨((18033230497/1152921504606846976), (6853117939/288230376151711744)), (399/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-41523047721/18446744073709551616), (-63119548827/18446744073709551616)), (231/9223372036854775808), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-2804091186185/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778899845164727/633825300114114700748351602688), (-1659490794129/316912650057057350374175801344)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944944499702459/19807040628566084398385987584), (-3733193743121/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472418218146547/618970019642690137449562112), (-1982856758935/1237940039285380274899124224)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771338675810685/154742504910672534362390528), (-3964808216157/154742504910672534362390528)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549691690615831/9671406556917033397649408), (-1858022999337/4835703278458516698824704)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258909192109455/604462909807314587353088), (-3250578746165/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943993491960839/37778931862957161709568), (-5280388072809/75557863725914323419136)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297684881375221/4722366482869645213696), (-3958714391471/4722366482869645213696)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621646817722211/590295810358705651712), (-1360167753257/147573952589676412928)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911860553936105/36893488147419103232), (-3398499128877/36893488147419103232)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822931586095621/9223372036854775808), (-7641344623209/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594176831762211/1152921504606846976), (-7634750026679/1152921504606846976)), (6715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597372100881149/72057594037927936), (-6672992062011/144115188075855872)), (5883/144115188075855872), by norm_num⟩
  | 4 => ⟨((745937628513491/18014398509481984), (-4997335724133/18014398509481984)), (8837/36028797018963968), by norm_num⟩
  | 3 => ⟨((744771131048923/4503599627370496), (-12467436691907/9007199254740992)), (173/140737488355328), by norm_num⟩
  | 2 => ⟨((278559899690275/562949953421312), (-776789737985/140737488355328)), (2777/562949953421312), by norm_num⟩
  | 1 => ⟨((1108402938919339/1125899906842624), (-4636534314751/281474976710656)), (16755/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090881323096039/1125899906842624), (-36706124085775/1125899906842624)), (33883/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090881323096039/1125899906842624), (-36706124085775/1125899906842624)), (129253391746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527877617854939/562949953421312), (-35564462671205/562949953421312)), (16967/281474976710656), by norm_num⟩
  | 2 => ⟨((1970974128277543/2251799813685248), (-266790093450689/2251799813685248)), (135855/1125899906842624), by norm_num⟩
  | 3 => ⟨((211695220263319/281474976710656), (-233518258895085/1125899906842624)), (270017/1125899906842624), by norm_num⟩
  | 4 => ⟨((1176848988535487/2251799813685248), (-351254664482083/1125899906842624)), (1036325/2251799813685248), by norm_num⟩
  | 5 => ⟨((98971296106955/562949953421312), (-734299193208641/2251799813685248)), (1729841/2251799813685248), by norm_num⟩
  | 6 => ⟨((-679403601639827/9007199254740992), (-129095921298995/1125899906842624)), (217053/281474976710656), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-38261558837/536870912)), (1/536870912), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-79690614991/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((216577027110707/4503599627370496), (263259782485331/2251799813685248)), (4959349/9007199254740992), by norm_num⟩
  | 1 => ⟨((-31697328461/274877906944), (-77059251457/274877906944)), (365/274877906944), by norm_num⟩
  | 2 => ⟨((19001718519/137438953472), (92390007397/274877906944)), (55/34359738368), by norm_num⟩
  | 3 => ⟨((-30376087341/274877906944), (-36923593665/137438953472)), (177/137438953472), by norm_num⟩
  | 4 => ⟨((4552417265/68719476736), (5533681919/34359738368)), (427/549755813888), by norm_num⟩
  | 5 => ⟨((-17465951743/549755813888), (-42461407087/549755813888)), (103/274877906944), by norm_num⟩
  | 6 => ⟨((27921015413/2199023255552), (67878671553/2199023255552)), (331/2199023255552), by norm_num⟩
  | 7 => ⟨((-4782262205/1099511627776), (-46504555897/4398046511104)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((22934727869/17592186044416), (27878263687/8796093022208)), (275/17592186044416), by norm_num⟩
  | 9 => ⟨((-24442255795/70368744177664), (-29710736315/35184372088832)), (295/70368744177664), by norm_num⟩
  | 10 => ⟨((23443987851/281474976710656), (56994587329/281474976710656)), (285/281474976710656), by norm_num⟩
  | 11 => ⟨((-10221132299/562949953421312), (-3106069353/70368744177664)), (251/1125899906842624), by norm_num⟩
  | 12 => ⟨((32678939763/9007199254740992), (4965352679/562949953421312)), (403/9007199254740992), by norm_num⟩
  | 13 => ⟨((-12055488489/18014398509481984), (-29308050995/18014398509481984)), (299/36028797018963968), by norm_num⟩
  | 14 => ⟨((16518742205/144115188075855872), (80317299355/288230376151711744)), (103/72057594037927936), by norm_num⟩
  | 15 => ⟨((-2640680923/144115188075855872), (-12839498163/288230376151711744)), (133/576460752303423488), by norm_num⟩
  | 16 => ⟨((25328305209/9223372036854775808), (15393885975/2305843009213693952)), (321/9223372036854775808), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (768902322553/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778777232044955/633825300114114700748351602688), (56872849135/19807040628566084398385987584)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944875659472889/19807040628566084398385987584), (2047051103859/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472381730363111/618970019642690137449562112), (1087266412655/1237940039285380274899124224)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221399137570803/19342813113834066795298816), (2174016644337/154742504910672534362390528)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193694451622297/1208925819614629174706176), (2037592316573/9671406556917033397649408)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258790523073657/604462909807314587353088), (1782345163643/604462909807314587353088)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471948723531079/18889465931478580854784), (1447641774145/37778931862957161709568)), (4605/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297541467444033/4722366482869645213696), (2170564106201/4722366482869645213696)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621450684346475/590295810358705651712), (2983066187189/590295810358705651712)), (4751/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823477530533421/73786976294838206464), (3726644758025/73786976294838206464)), (5941/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822659744083891/9223372036854775808), (2094734427377/4611686018427387904)), (3343/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796953856757899/576460752303423488), (4185713683753/1152921504606846976)), (3345/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194511781553833/144115188075855872), (914569740313/36028797018963968)), (5857/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491532728299825/36028797018963968), (5478987547149/36028797018963968)), (8793/36028797018963968), by norm_num⟩
  | 3 => ⟨((744562372712161/4503599627370496), (3417001567183/4503599627370496)), (11005/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227675962976243/4503599627370496), (3405975827737/1125899906842624)), (11025/2251799813685248), by norm_num⟩
  | 1 => ⟨((553920013871813/562949953421312), (20325915308241/2251799813685248)), (4147/281474976710656), by norm_num⟩
  | 0 => ⟨((1089912161601659/1125899906842624), (40213973951225/2251799813685248)), (66761/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089912161601659/1125899906842624), (40213973951225/2251799813685248)), (254673012740325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2109431259146467/2251799813685248), (77857186077375/2251799813685248)), (16455/281474976710656), by norm_num⟩
  | 2 => ⟨((1973371908388249/2251799813685248), (72934716959593/1125899906842624)), (127869/1125899906842624), by norm_num⟩
  | 3 => ⟨((429980362100399/562949953421312), (127833141045305/1125899906842624)), (481367/2251799813685248), by norm_num⟩
  | 4 => ⟨((1284645519238929/2251799813685248), (390555074681427/2251799813685248)), (844643/2251799813685248), by norm_num⟩
  | 5 => ⟨((1330296622851217/4503599627370496), (891242327415257/4503599627370496)), (2513451/4503599627370496), by norm_num⟩
  | 6 => ⟨((216577027110707/4503599627370496), (263259782485331/2251799813685248)), (4959349/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-79690614991/1073741824)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2301277821/1073741824), (-20645578371/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((30746480562099/4503599627370496), (-2109059348830557/18014398509481984)), (2610667/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4663216187/274877906944), (79968499767/274877906944)), (199/137438953472), by norm_num⟩
  | 2 => ⟨((724228557/34359738368), (-99357128423/274877906944)), (497/274877906944), by norm_num⟩
  | 3 => ⟨((-4799040953/274877906944), (20574432427/68719476736)), (207/137438953472), by norm_num⟩
  | 4 => ⟨((1490646097/137438953472), (-102251087907/549755813888)), (517/549755813888), by norm_num⟩
  | 5 => ⟨((-2963293119/549755813888), (25408440829/274877906944)), (129/274877906944), by norm_num⟩
  | 6 => ⟨((2454502259/1099511627776), (-21045867859/549755813888)), (429/2199023255552), by norm_num⟩
  | 7 => ⟨((-6970524555/8796093022208), (119536038843/8796093022208)), (153/2199023255552), by norm_num⟩
  | 8 => ⟨((4330275705/17592186044416), (-74258974453/17592186044416)), (191/8796093022208), by norm_num⟩
  | 9 => ⟨((-4782369287/70368744177664), (10251478857/8796093022208)), (53/8796093022208), by norm_num⟩
  | 10 => ⟨((4753496497/281474976710656), (-81516697543/281474976710656)), (53/35184372088832), by norm_num⟩
  | 11 => ⟨((-4295270929/1125899906842624), (9207335627/140737488355328)), (385/1125899906842624), by norm_num⟩
  | 12 => ⟨((7115564863/9007199254740992), (-122023304141/9007199254740992)), (5/70368744177664), by norm_num⟩
  | 13 => ⟨((-5440465983/36028797018963968), (5831086921/2251799813685248)), (123/9007199254740992), by norm_num⟩
  | 14 => ⟨((3862585743/144115188075855872), (-66238659043/144115188075855872)), (351/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1279755333/288230376151711744), (5486562811/72057594037927936)), (467/1152921504606846976), by norm_num⟩
  | 16 => ⟨((3180072537/4611686018427387904), (-109068771309/9223372036854775808)), (291/4611686018427387904), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (-1970264112907/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444665102424115/158456325028528675187087900672), (-1165720554279/316912650057057350374175801344)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472404963534419/9903520314283042199192993792), (-1311188685563/19807040628566084398385987584)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889387186280477/2475880078570760549798248448), (-2785666498809/2475880078570760549798248448)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771053304927747/154742504910672534362390528), (-2784981061265/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549424490378941/9671406556917033397649408), (-1305095833513/4835703278458516698824704)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314668931668981/151115727451828646838272), (-570797463777/151115727451828646838272)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887608229884873/75557863725914323419136), (-927204816457/18889465931478580854784)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((648700682160395/2361183241434822606848), (-695105302065/1180591620717411303424)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202657234034597/73786976294838206464), (-119410657429/18446744073709551616)), (1189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455809065121221/18446744073709551616), (-1193380168543/18446744073709551616)), (5947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455596991360037/2305843009213693952), (-670777258087/1152921504606846976)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199204437333869/144115188075855872), (-5361231002327/1152921504606846976)), (3349/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194273104345607/144115188075855872), (-4685471910279/144115188075855872)), (2933/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491173737810911/36028797018963968), (-3508505246645/18014398509481984)), (1101/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488674310073795/9007199254740992), (-8751697077011/9007199254740992)), (2757/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113385017121549/2251799813685248), (-8722406674635/2251799813685248)), (11053/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214308634793379/2251799813685248), (-26021178015343/2251799813685248)), (16645/1125899906842624), by norm_num⟩
  | 0 => ⟨((2177032073042215/2251799813685248), (-25730321625433/1125899906842624)), (67105/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177032073042215/2251799813685248), (-25730321625433/1125899906842624)), (255985268599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051785425254679/1125899906842624), (-99503934742023/2251799813685248)), (66411/1125899906842624), by norm_num⟩
  | 2 => ⟨((1960702396034861/2251799813685248), (-92953900858419/1125899906842624)), (259897/2251799813685248), by norm_num⟩
  | 3 => ⟨((422971899180797/562949953421312), (-161874901157945/1125899906842624)), (247757/1125899906842624), by norm_num⟩
  | 4 => ⟨((306162840129763/562949953421312), (-243249098632531/1125899906842624)), (887093/2251799813685248), by norm_num⟩
  | 5 => ⟨((1121849687705465/4503599627370496), (-264584211948959/1125899906842624)), (674105/1125899906842624), by norm_num⟩
  | 6 => ⟨((30746480562099/4503599627370496), (-2109059348830557/18014398509481984)), (2610667/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-20645578371/268435456)), (1/536870912), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2375405559/1073741824), (-10655302279/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-651853428948093/9007199254740992), (739594353761921/9007199254740992)), (5608359/9007199254740992), by norm_num⟩
  | 1 => ⟨((51024506645/274877906944), (-14473129749/68719476736)), (441/274877906944), by norm_num⟩
  | 2 => ⟨((-8179704721/34359738368), (18561422425/68719476736)), (285/137438953472), by norm_num⟩
  | 3 => ⟨((55948075649/274877906944), (-15869702841/68719476736)), (245/137438953472), by norm_num⟩
  | 4 => ⟨((-8968998793/68719476736), (40704984105/274877906944)), (79/68719476736), by norm_num⟩
  | 5 => ⟨((18404022153/274877906944), (-20881244565/274877906944)), (163/274877906944), by norm_num⟩
  | 6 => ⟨((-31470256531/1099511627776), (8926555805/274877906944)), (35/137438953472), by norm_num⟩
  | 7 => ⟨((11531373467/1099511627776), (-52334088175/4398046511104)), (103/1099511627776), by norm_num⟩
  | 8 => ⟨((-29577388965/8796093022208), (67117142919/17592186044416)), (531/17592186044416), by norm_num⟩
  | 9 => ⟨((16858778849/17592186044416), (-38256016135/35184372088832)), (305/35184372088832), by norm_num⟩
  | 10 => ⟨((-34593531181/140737488355328), (19624948801/70368744177664)), (315/140737488355328), by norm_num⟩
  | 11 => ⟨((32265692937/562949953421312), (-9152181785/140737488355328)), (37/70368744177664), by norm_num⟩
  | 12 => ⟨((-27586622789/2251799813685248), (62599687437/4503599627370496)), (127/1125899906842624), by norm_num⟩
  | 13 => ⟨((21771781661/9007199254740992), (-49404624021/18014398509481984)), (403/18014398509481984), by norm_num⟩
  | 14 => ⟨((-63821162723/144115188075855872), (18102908377/36028797018963968)), (593/144115188075855872), by norm_num⟩
  | 15 => ⟨((43652813419/576460752303423488), (-1547768107/18014398509481984)), (51/72057594037927936), by norm_num⟩
  | 16 => ⟨((-27991813933/2305843009213693952), (63519148985/4611686018427387904)), (263/2305843009213693952), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (186698490227/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889275111525711/316912650057057350374175801344), (3534364212787/633825300114114700748351602688)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889495705718033/39614081257132168796771975168), (993844972813/9903520314283042199192993792)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889255029371979/2475880078570760549798248448), (2111443275103/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770920867916755/154742504910672534362390528), (2110906421971/77371252455336267181195264)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774650016645833/4835703278458516698824704), (1978404488901/4835703278458516698824704)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157320816197741/75557863725914323419136), (3461067572607/604462909807314587353088)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235928778498619/9444732965739290427392), (175690542839/2361183241434822606848)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297267376381887/4722366482869645213696), (4214703368789/4722366482869645213696)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621072849252451/590295810358705651712), (5792180053141/590295810358705651712)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823003799008677/73786976294838206464), (7235671403755/73786976294838206464)), (5961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822124822859841/9223372036854775808), (8133872221375/9223372036854775808)), (839/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199171291374069/144115188075855872), (8126054354467/1152921504606846976)), (6719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194038810127101/144115188075855872), (3550754508211/72057594037927936)), (5887/144115188075855872), by norm_num⟩
  | 4 => ⟨((186352220725097/4503599627370496), (2658675707617/9007199254740992)), (2211/9007199254740992), by norm_num⟩
  | 3 => ⟨((744110724261483/4503599627370496), (13262684213551/9007199254740992)), (11081/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112920374930011/2251799813685248), (6608358260121/1125899906842624)), (11121/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106428126436493/1125899906842624), (9855206940509/562949953421312)), (4195/281474976710656), by norm_num⟩
  | 0 => ⟨((1061472736579/1099511627776), (19481867302473/562949953421312)), (33957/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1061472736579/1099511627776), (19481867302473/562949953421312)), (129535679343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523997716731541/562949953421312), (9403934654631/140737488355328)), (67915/1125899906842624), by norm_num⟩
  | 2 => ⟨((1940909039518965/2251799813685248), (280103920847481/2251799813685248)), (33877/281474976710656), by norm_num⟩
  | 3 => ⟨((1638098409456523/2251799813685248), (120715933244493/562949953421312)), (267311/1125899906842624), by norm_num⟩
  | 4 => ⟨((272027846297381/562949953421312), (702529868035611/2251799813685248)), (503559/1125899906842624), by norm_num⟩
  | 5 => ⟨((613232283705517/4503599627370496), (169737723397843/562949953421312)), (800865/1125899906842624), by norm_num⟩
  | 6 => ⟨((-651853428948093/9007199254740992), (739594353761921/9007199254740992)), (5608359/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-10655302279/134217728)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-5481580659/67108864)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1849627522284523/18014398509481984), (-234904334907/4503599627370496)), (1786299/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2327572379/8589934592), (37837281/274877906944)), (73/137438953472), by norm_num⟩
  | 2 => ⟨((6142596947/17179869184), (-49927377/274877906944)), (195/274877906944), by norm_num⟩
  | 3 => ⟨((-86456882645/274877906944), (43920403/274877906944)), (87/137438953472), by norm_num⟩
  | 4 => ⟨((14260291865/68719476736), (-57954231/549755813888)), (29/68719476736), by norm_num⟩
  | 5 => ⟨((-30106982215/274877906944), (61177815/1099511627776)), (247/1099511627776), by norm_num⟩
  | 6 => ⟨((26484684029/549755813888), (-26908627/1099511627776)), (55/549755813888), by norm_num⟩
  | 7 => ⟨((-79879542297/4398046511104), (40579091/4398046511104)), (21/549755813888), by norm_num⟩
  | 8 => ⟨((105403345793/17592186044416), (-26772637/8796093022208)), (7/549755813888), by norm_num⟩
  | 9 => ⟨((-15453637349/8796093022208), (62804021/70368744177664)), (265/70368744177664), by norm_num⟩
  | 10 => ⟨((130505711729/281474976710656), (-66297365/281474976710656)), (141/140737488355328), by norm_num⟩
  | 11 => ⟨((-31310186827/281474976710656), (7952843/140737488355328)), (273/1125899906842624), by norm_num⟩
  | 12 => ⟨((55086252025/2251799813685248), (-55968023/4503599627370496)), (121/2251799813685248), by norm_num⟩
  | 13 => ⟨((-89462016719/18014398509481984), (22723511/9007199254740992)), (99/9007199254740992), by norm_num⟩
  | 14 => ⟨((134911651969/144115188075855872), (-34267799/72057594037927936)), (301/144115188075855872), by norm_num⟩
  | 15 => ⟨((-94943889061/576460752303423488), (48231833/576460752303423488)), (107/288230376151711744), by norm_num⟩
  | 16 => ⟨((125281183165/4611686018427387904), (-31821643/2305843009213693952)), (285/4611686018427387904), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-41358205/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778458405865349/633825300114114700748351602688), (-782864051/633825300114114700748351602688)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944696403870981/19807040628566084398385987584), (-880548001/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889146218447479/2475880078570760549798248448), (-935365109/2475880078570760549798248448)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770812639443323/154742504910672534362390528), (-935120927/154742504910672534362390528)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12103118652677/75557863725914323419136), (-219104129/2417851639229258349412352)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258478907535691/604462909807314587353088), (-47912825/37778931862957161709568)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887288999905683/75557863725914323419136), (-1245247569/75557863725914323419136)), (287/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((162145308420721/590295810358705651712), (-933510747/4722366482869645213696)), (861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620930242098503/590295810358705651712), (-641443585/295147905179352825856)), (4735/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822828000977527/73786976294838206464), (-1602574509/73786976294838206464)), (5919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113870651789183/576460752303423488), (-225184387/1152921504606846976)), (6659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796590076078489/576460752303423488), (-1799700281/1152921504606846976)), (6659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193877135266659/144115188075855872), (-786371721/72057594037927936)), (5827/144115188075855872), by norm_num⟩
  | 4 => ⟨((745292345019787/18014398509481984), (-588783113/9007199254740992)), (8739/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487946557759955/9007199254740992), (-1468479533/4503599627370496)), (2731/2251799813685248), by norm_num⟩
  | 2 => ⟨((2225340090765165/4503599627370496), (-2926550759/2251799813685248)), (2731/562949953421312), by norm_num⟩
  | 1 => ⟨((2212227235015575/2251799813685248), (-272743605/70368744177664)), (8193/562949953421312), by norm_num⟩
  | 0 => ⟨((543280255139725/562949953421312), (-17249267013/2251799813685248)), (65551/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543280255139725/562949953421312), (-17249267013/2251799813685248)), (250057229048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524297824011357/562949953421312), (-16646570671/1125899906842624)), (126523/2251799813685248), by norm_num⟩
  | 2 => ⟨((976599097390955/1125899906842624), (-62014470217/2251799813685248)), (235677/2251799813685248), by norm_num⟩
  | 3 => ⟨((423548216971605/562949953421312), (-53790994449/1125899906842624)), (12777/70368744177664), by norm_num⟩
  | 4 => ⟨((1274664579230901/2251799813685248), (-10117719901/140737488355328)), (153819/562949953421312), by norm_num⟩
  | 5 => ⟨((1443085440779527/4503599627370496), (-91636559179/1125899906842624)), (696661/2251799813685248), by norm_num⟩
  | 6 => ⟨((1849627522284523/18014398509481984), (-234904334907/4503599627370496)), (1786299/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5481580659/67108864)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2507931583/1073741824), (-22499542453/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-466644073321871/9007199254740992), (-91988327354259/1125899906842624)), (1228851/2251799813685248), by norm_num⟩
  | 1 => ⟨((38564928485/274877906944), (60817629001/274877906944)), (51/34359738368), by norm_num⟩
  | 2 => ⟨((-52217881169/274877906944), (-82348596223/274877906944)), (555/274877906944), by norm_num⟩
  | 3 => ⟨((47136214533/274877906944), (37167355427/137438953472)), (503/274877906944), by norm_num⟩
  | 4 => ⟨((-31911808811/274877906944), (-50325532169/274877906944)), (171/137438953472), by norm_num⟩
  | 5 => ⟨((34567512107/549755813888), (13628406751/137438953472)), (93/137438953472), by norm_num⟩
  | 6 => ⟨((-31203519371/1099511627776), (-24604273095/549755813888)), (337/1099511627776), by norm_num⟩
  | 7 => ⟨((48286112519/4398046511104), (38074060973/2199023255552)), (131/1099511627776), by norm_num⟩
  | 8 => ⟨((-32690304179/8796093022208), (-51553234237/8796093022208)), (357/8796093022208), by norm_num⟩
  | 9 => ⟨((9836331645/8796093022208), (15512082927/8796093022208)), (27/2199023255552), by norm_num⟩
  | 10 => ⟨((-42619647823/140737488355328), (-4200749929/8796093022208)), (235/70368744177664), by norm_num⟩
  | 11 => ⟨((41969507585/562949953421312), (66186715287/562949953421312)), (465/562949953421312), by norm_num⟩
  | 12 => ⟨((-18942588909/1125899906842624), (-29872824607/1125899906842624)), (211/1125899906842624), by norm_num⟩
  | 13 => ⟨((31567681049/9007199254740992), (49782836113/9007199254740992)), (177/4503599627370496), by norm_num⟩
  | 14 => ⟨((-24424818575/36028797018963968), (-77036811055/72057594037927936)), (275/36028797018963968), by norm_num⟩
  | 15 => ⟨((35276605255/288230376151711744), (55631880445/288230376151711744)), (399/288230376151711744), by norm_num⟩
  | 16 => ⟨((-47765408977/2305843009213693952), (-75326962513/2305843009213693952)), (543/2305843009213693952), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (-2782271966731/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222295113008441/79228162514264337593543950336), (-1645627755649/316912650057057350374175801344)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889282815857231/39614081257132168796771975168), (-3701900493293/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472257237980381/618970019642690137449562112), (-491541393741/309485009821345068724781056)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770694923194661/154742504910672534362390528), (-3931276024979/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((6051126371417/37778931862957161709568), (-1842225246697/4835703278458516698824704)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258381448554435/604462909807314587353088), (-3222773727983/604462909807314587353088)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471782433845855/18889465931478580854784), (-1308726787625/18889465931478580854784)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648521118925289/2361183241434822606848), (-981085854571/1180591620717411303424)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620763658771649/590295810358705651712), (-5392988464739/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((14239202132579/576460752303423488), (-1684190562919/18446744073709551616)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910845714096023/4611686018427387904), (-1893177599933/2305843009213693952)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592937900416641/1152921504606846976), (-3782516011609/576460752303423488)), (3357/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193661516512497/144115188075855872), (-6610772462563/144115188075855872)), (5883/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490253987998777/36028797018963968), (-4949458305935/18014398509481984)), (8837/36028797018963968), by norm_num⟩
  | 3 => ⟨((743760251313535/4503599627370496), (-12343514930159/9007199254740992)), (5535/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224450154244685/4503599627370496), (-6149202126919/1125899906842624)), (22213/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105399242426687/1125899906842624), (-9167564507695/562949953421312)), (33505/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084946220290595/1125899906842624), (-72444285989337/2251799813685248)), (8469/281474976710656), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084946220290595/1125899906842624), (-72444285989337/2251799813685248)), (32306672216319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2088633723360051/2251799813685248), (-69809184447129/1125899906842624)), (134935/2251799813685248), by norm_num⟩
  | 2 => ⟨((964316968815421/1125899906842624), (-4046924374405/35184372088832)), (267049/2251799813685248), by norm_num⟩
  | 3 => ⟨((1622056368560359/2251799813685248), (-221832456517829/1125899906842624)), (16215/70368744177664), by norm_num⟩
  | 4 => ⟨((1081014525773707/2251799813685248), (-639177153601859/2251799813685248)), (952005/2251799813685248), by norm_num⟩
  | 5 => ⟨((337527770731673/2251799813685248), (-1227391144429471/4503599627370496)), (1454509/2251799813685248), by norm_num⟩
  | 6 => ⟨((-466644073321871/9007199254740992), (-91988327354259/1125899906842624)), (1228851/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-22499542453/268435456)), (1/536870912), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile059Terms1

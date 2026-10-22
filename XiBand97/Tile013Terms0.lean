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
namespace Reinmann.XiBand97.Tile013Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5149/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5149/256))
  have he : value ((69/80), (5149/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-1871191649/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((240831099275725/2251799813685248), (-1214845714505965/2251799813685248)), (45599591/2251799813685248), by norm_num⟩
  | 1 => ⟨((-318396373/4294967296), (401528779/1073741824)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((55173887/2147483648), (-278318541/2147483648)), (45/8589934592), by norm_num⟩
  | 3 => ⟨((-50991499/8589934592), (1028883797/34359738368)), (43/34359738368), by norm_num⟩
  | 4 => ⟨((141378455/137438953472), (-713167903/137438953472)), (31/137438953472), by norm_num⟩
  | 5 => ⟨((-39198431/274877906944), (395464257/549755813888)), (71/2199023255552), by norm_num⟩
  | 6 => ⟨((289816341/17592186044416), (-1461946319/17592186044416)), (17/4398046511104), by norm_num⟩
  | 7 => ⟨((-229583291/140737488355328), (1158107393/140737488355328)), (7/17592186044416), by norm_num⟩
  | 8 => ⟨((159135011/1125899906842624), (-1605477749/2251799813685248)), (5/140737488355328), by norm_num⟩
  | 9 => ⟨((-49023993/4503599627370496), (494592167/9007199254740992)), (51/18014398509481984), by norm_num⟩
  | 10 => ⟨((13592337/18014398509481984), (-274260133/72057594037927936)), (59/288230376151711744), by norm_num⟩
  | 11 => ⟨((-219263769/4611686018427387904), (8641029/36028797018963968)), (61/4611686018427387904), by norm_num⟩
  | 12 => ⟨((202642751/73786976294838206464), (-511104417/36893488147419103232)), (29/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-345750773/2361183241434822606848), (1744101345/2361183241434822606848)), (101/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((136946385/18889465931478580854784), (-690810817/18889465931478580854784)), (41/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-202504535/604462909807314587353088), (15961119/9444732965739290427392)), (31/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((280730895/19342813113834066795298816), (-1416115793/19342813113834066795298816)), (11/2417851639229258349412352), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1791212916391/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890523009275271/316912650057057350374175801344), (-2124973819199/633825300114114700748351602688)), (23103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473075839193385/9903520314283042199192993792), (-2390463428221/39614081257132168796771975168)), (12997/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((946119022577015/1237940039285380274899124224), (-2539711993871/2475880078570760549798248448)), (13811/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886951877865861/77371252455336267181195264), (-2539537153765/154742504910672534362390528)), (13813/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776048177207727/4835703278458516698824704), (-2380630301215/9671406556917033397649408)), (25905/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157626646761875/75557863725914323419136), (-2082865718699/604462909807314587353088)), (1417/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((59106430277281/2361183241434822606848), (-3384308396881/75557863725914323419136)), (36849/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325062201770977/1180591620717411303424), (-634481605137/1180591620717411303424)), (27645/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406292987460755/147573952589676412928), (-872288336401/147573952589676412928)), (4753/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828127122951499/73786976294838206464), (-4360698357785/73786976294838206464)), (11887/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827887800560921/9223372036854775808), (-4904763418997/9223372036854775808)), (53517/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799566176004105/576460752303423488), (-2451742691689/576460752303423488)), (13387/288230376151711744), by norm_num⟩
  | 5 => ⟨((299769874011123/36028797018963968), (-4289111585797/144115188075855872)), (46891/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498376614266425/36028797018963968), (-6430790294529/36028797018963968)), (70407/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497666158674039/9007199254740992), (-8033451096919/9007199254740992)), (88135/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122359240233523/2251799813685248), (-250809131353/70368744177664)), (88323/2251799813685248), by norm_num⟩
  | 1 => ⟨((560285785538635/562949953421312), (-12019928042339/1125899906842624)), (33239/281474976710656), by norm_num⟩
  | 0 => ⟨((69698382447327/70368744177664), (-23964137263637/1125899906842624)), (267801/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((69698382447327/70368744177664), (-23964137263637/1125899906842624)), (1021579746726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((552020223382551/562949953421312), (-47471689982251/1125899906842624)), (541901/1125899906842624), by norm_num⟩
  | 2 => ⟨((270150956437013/281474976710656), (-46550022340507/562949953421312)), (1108457/1125899906842624), by norm_num⟩
  | 3 => ⟨((257357914957117/281474976710656), (-178709073245675/1125899906842624)), (1155521/562949953421312), by norm_num⟩
  | 4 => ⟨((912863215593577/1125899906842624), (-326794196854689/1125899906842624)), (4959703/1125899906842624), by norm_num⟩
  | 5 => ⟨((322641825827727/562949953421312), (-264959966303461/562949953421312)), (5460817/562949953421312), by norm_num⟩
  | 6 => ⟨((240831099275725/2251799813685248), (-1214845714505965/2251799813685248)), (45599591/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1871191649/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-741442149/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1736277035829339/4503599627370496), (183946570725943/4503599627370496)), (4459761/140737488355328), by norm_num⟩
  | 1 => ⟨((1819129265/4294967296), (-192724193/4294967296)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-999258883/4294967296), (105864583/4294967296)), (85/4294967296), by norm_num⟩
  | 3 => ⟨((1463730785/17179869184), (-9692011/1073741824)), (127/17179869184), by norm_num⟩
  | 4 => ⟨((-402018157/17179869184), (85182099/34359738368)), (71/34359738368), by norm_num⟩
  | 5 => ⟨((1413318681/274877906944), (-149731361/274877906944)), (127/274877906944), by norm_num⟩
  | 6 => ⟨((-1035126181/1099511627776), (109664475/1099511627776)), (95/1099511627776), by norm_num⟩
  | 7 => ⟨((1299659821/8796093022208), (-34422497/2199023255552)), (61/4398046511104), by norm_num⟩
  | 8 => ⟨((-1427822251/70368744177664), (151267913/70368744177664)), (17/8796093022208), by norm_num⟩
  | 9 => ⟨((1394331619/562949953421312), (-36929953/140737488355328)), (135/562949953421312), by norm_num⟩
  | 10 => ⟨((-1225463881/4503599627370496), (129829441/4503599627370496)), (121/4503599627370496), by norm_num⟩
  | 11 => ⟨((122391789/4503599627370496), (-103732523/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | 12 => ⟨((-89640749/36028797018963968), (151949099/576460752303423488)), (73/288230376151711744), by norm_num⟩
  | 13 => ⟨((1939306899/9223372036854775808), (-205456181/9223372036854775808)), (201/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-1217455081/73786976294838206464), (128980963/73786976294838206464)), (1/576460752303423488), by norm_num⟩
  | 15 => ⟨((1426678521/1180591620717411303424), (-75573371/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 16 => ⟨((-391841639/4722366482869645213696), (41512917/4722366482869645213696)), (85/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (3954785338287/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445124107719533/158456325028528675187087900672), (2344494254471/316912650057057350374175801344)), (46331/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891684558648003/39614081257132168796771975168), (2637315012159/19807040628566084398385987584)), (52137/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891579934929317/2475880078570760549798248448), (1400937057069/618970019642690137449562112)), (55413/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773244928811991/154742504910672534362390528), (5603133483051/154742504910672534362390528)), (6929/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775738971473323/4835703278458516698824704), (5252284247985/9671406556917033397649408)), (12997/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260471303116945/604462909807314587353088), (4595095071035/604462909807314587353088)), (22755/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118157737648717/4722366482869645213696), (1866450841457/18889465931478580854784)), (9249/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649793042471345/2361183241434822606848), (2799139563675/2361183241434822606848)), (6941/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624258681234627/590295810358705651712), (1923972130545/147573952589676412928)), (76405/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826982500710141/73786976294838206464), (9617240974177/73786976294838206464)), (23897/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826595928654655/9223372036854775808), (1351973897359/1152921504606846976)), (107649/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798917635081509/576460752303423488), (10811280750263/1152921504606846976)), (53895/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197938695013291/144115188075855872), (4727395273245/72057594037927936)), (94475/144115188075855872), by norm_num⟩
  | 4 => ⟨((748326860404563/18014398509481984), (14172010936177/36028797018963968)), (71015/18014398509481984), by norm_num⟩
  | 3 => ⟨((747746059558077/4503599627370496), (17697174716003/9007199254740992)), (89047/4503599627370496), by norm_num⟩
  | 2 => ⟨((140019330357749/281474976710656), (17670350681369/2251799813685248)), (178931/2251799813685248), by norm_num⟩
  | 1 => ⟨((139648568480703/140737488355328), (26438237281003/1125899906842624)), (135245/562949953421312), by norm_num⟩
  | 0 => ⟨((554052585435237/562949953421312), (6575744416087/140737488355328)), (137345/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554052585435237/562949953421312), (6575744416087/140737488355328)), (523929597021007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((544066872964527/562949953421312), (12943630860087/140737488355328)), (1132733/1125899906842624), by norm_num⟩
  | 2 => ⟨((521055484945385/562949953421312), (1563682687079/8796093022208)), (2397831/1125899906842624), by norm_num⟩
  | 3 => ⟨((232244156588543/281474976710656), (185256212902607/562949953421312)), (5291297/1125899906842624), by norm_num⟩
  | 4 => ⟨((161141792051359/281474976710656), (19106793000369/35184372088832)), (12214199/1125899906842624), by norm_num⟩
  | 5 => ⟨((18489932535819/562949953421312), (1400122921238027/2251799813685248)), (212897/8796093022208), by norm_num⟩
  | 6 => ⟨((-1736277035829339/4503599627370496), (183946570725943/4503599627370496)), (4459761/140737488355328), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-741442149/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-1871191649/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1259304209067189/4503599627370496), (-259856695161577/2251799813685248)), (59512125/2251799813685248), by norm_num⟩
  | 1 => ⟨((832446253/2147483648), (171774803/1073741824)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-1154015547/4294967296), (-238130441/2147483648)), (115/4294967296), by norm_num⟩
  | 3 => ⟨((533268415/4294967296), (440158517/8589934592)), (27/2147483648), by norm_num⟩
  | 4 => ⟨((-1478533993/34359738368), (-305094635/17179869184)), (19/4294967296), by norm_num⟩
  | 5 => ⟨((819873335/68719476736), (169180389/34359738368)), (43/34359738368), by norm_num⟩
  | 6 => ⟨((-378861927/137438953472), (-312711759/274877906944)), (161/549755813888), by norm_num⟩
  | 7 => ⟨((1200489493/2199023255552), (247720313/1099511627776)), (65/1099511627776), by norm_num⟩
  | 8 => ⟨((-832115907/8796093022208), (-343413273/8796093022208)), (23/2199023255552), by norm_num⟩
  | 9 => ⟨((256346131/17592186044416), (13224219/2199023255552)), (115/70368744177664), by norm_num⟩
  | 10 => ⟨((-1137187827/562949953421312), (-234658051/281474976710656)), (129/562949953421312), by norm_num⟩
  | 11 => ⟨((286632195/1125899906842624), (236585551/2251799813685248)), (33/1125899906842624), by norm_num⟩
  | 12 => ⟨((-264904397/9007199254740992), (-218651477/18014398509481984)), (31/9007199254740992), by norm_num⟩
  | 13 => ⟨((451982119/144115188075855872), (93266249/72057594037927936)), (27/72057594037927936), by norm_num⟩
  | 14 => ⟨((-716091729/2305843009213693952), (-295530229/2305843009213693952)), (87/2305843009213693952), by norm_num⟩
  | 15 => ⟨((529447427/18446744073709551616), (437004683/36893488147419103232)), (131/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-1467939965/590295810358705651712), (-75727141/73786976294838206464)), (23/73786976294838206464), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-3582425832781/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222514424713553/79228162514264337593543950336), (-4245764600369/633825300114114700748351602688)), (46309/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236407008775311/4951760157141521099596496896), (-4775951108147/39614081257132168796771975168)), (52111/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891124872284501/2475880078570760549798248448), (-5073825832137/2475880078570760549798248448)), (55383/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886395049167533/77371252455336267181195264), (-5073125655039/154742504910672534362390528)), (55401/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193881473256553/1208925819614629174706176), (-4755311262043/9671406556917033397649408)), (51957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157512332813987/75557863725914323419136), (-2080076600343/302231454903657293676544)), (45481/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889918723915143/75557863725914323419136), (-3379426710551/37778931862957161709568)), (73941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649566340398513/2361183241434822606848), (-5067918735437/4722366482869645213696)), (27743/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623635908172931/590295810358705651712), (-1741600786775/147573952589676412928)), (76343/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114137813802165/4611686018427387904), (-8705025472881/73786976294838206464)), (95503/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825722620153941/9223372036854775808), (-4894528496361/4611686018427387904)), (107543/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798481828545491/576460752303423488), (-9783934247095/1152921504606846976)), (107671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197177940900099/144115188075855872), (-8555176752475/144115188075855872)), (23589/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495516404194673/36028797018963968), (-1602653395605/4503599627370496)), (141821/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494077148571157/9007199254740992), (-8003163941705/4503599627370496)), (44445/2251799813685248), by norm_num⟩
  | 2 => ⟨((139843710570371/281474976710656), (-7987994840097/1125899906842624)), (89269/1125899906842624), by norm_num⟩
  | 1 => ⟨((557553069271325/562949953421312), (-11944018990095/562949953421312)), (33713/140737488355328), by norm_num⟩
  | 0 => ⟨((1104040446765103/1125899906842624), (-11867922495563/281474976710656)), (547015/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104040446765103/1125899906842624), (-11867922495563/281474976710656)), (2086696629050826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((540301912874027/562949953421312), (-11637505585127/140737488355328)), (559459/562949953421312), by norm_num⟩
  | 2 => ⟨((1029431659828471/1125899906842624), (-178709073245679/1125899906842624)), (583213/281474976710656), by norm_num⟩
  | 3 => ⟨((912863215593581/1125899906842624), (-163397098427349/562949953421312)), (5006509/1125899906842624), by norm_num⟩
  | 4 => ⟨((20165114114233/35184372088832), (-529919932606939/1125899906842624)), (172261/17592186044416), by norm_num⟩
  | 5 => ⟨((240831099275697/2251799813685248), (-151855714313251/281474976710656)), (46029925/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1259304209067189/4503599627370496), (-259856695161577/2251799813685248)), (59512125/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1871191649/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-1086193115/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((648991950623397/4503599627370496), (-28671579770653/140737488355328)), (8689545/562949953421312), by norm_num⟩
  | 1 => ⟨((-498062253/2147483648), (704118767/2147483648)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((801600273/4294967296), (-1133235439/4294967296)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((-860083913/8589934592), (37997335/268435456)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((692125829/17179869184), (-122308703/2147483648)), (83/17179869184), by norm_num⟩
  | 5 => ⟨((-111393355/8589934592), (157478611/8589934592)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((478081837/137438953472), (-675872125/137438953472)), (61/137438953472), by norm_num⟩
  | 7 => ⟨((-879363467/1099511627776), (310792635/274877906944)), (115/1099511627776), by norm_num⟩
  | 8 => ⟨((707640451/4398046511104), (-250100725/1099511627776)), (95/4398046511104), by norm_num⟩
  | 9 => ⟨((-126544819/4398046511104), (44724621/1099511627776)), (35/8796093022208), by norm_num⟩
  | 10 => ⟨((325865647/70368744177664), (-921363209/140737488355328)), (23/35184372088832), by norm_num⟩
  | 11 => ⟨((-762851675/1125899906842624), (1078455913/1125899906842624)), (55/562949953421312), by norm_num⟩
  | 12 => ⟨((51156767/562949953421312), (-289284639/2251799813685248)), (15/1125899906842624), by norm_num⟩
  | 13 => ⟨((-810669689/72057594037927936), (1146057023/72057594037927936)), (121/72057594037927936), by norm_num⟩
  | 14 => ⟨((745555733/576460752303423488), (-263501089/144115188075855872)), (113/576460752303423488), by norm_num⟩
  | 15 => ⟨((-639960353/4611686018427387904), (452361219/2305843009213693952)), (99/4611686018427387904), by norm_num⟩
  | 16 => ⟨((514988227/36893488147419103232), (-11375739/576460752303423488)), (81/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-622095314347/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779826782149113/633825300114114700748351602688), (-1474103107843/633825300114114700748351602688)), (46173/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890931915857439/39614081257132168796771975168), (-207270118007/4951760157141521099596496896)), (51949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890781129426091/2475880078570760549798248448), (-1761546359203/2475880078570760549798248448)), (55201/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772447110266401/154742504910672534362390528), (-880632780559/77371252455336267181195264)), (6901/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96920689776369/604462909807314587353088), (-412722042255/2417851639229258349412352)), (12941/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629909403977011/302231454903657293676544), (-1444228913475/604462909807314587353088)), (11325/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944732731077869/37778931862957161709568), (-1173156461287/37778931862957161709568)), (9203/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298794047968049/4722366482869645213696), (-879622820261/2361183241434822606848)), (55229/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623172421200121/590295810358705651712), (-1209084143267/295147905179352825856)), (18989/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825628859672665/73786976294838206464), (-3021519073159/73786976294838206464)), (94971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825078831914211/9223372036854775808), (-1698785810353/4611686018427387904)), (106877/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596325354831693/1152921504606846976), (-3395525970039/1152921504606846976)), (53461/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196625590789651/144115188075855872), (-2968785268815/144115188075855872)), (46803/72057594037927936), by norm_num⟩
  | 4 => ⟨((747350094679103/18014398509481984), (-1112145374157/9007199254740992)), (140509/36028797018963968), by norm_num⟩
  | 3 => ⟨((373269595423567/2251799813685248), (-694086379625/1125899906842624)), (175811/9007199254740992), by norm_num⟩
  | 2 => ⟨((279445771844151/562949953421312), (-2770326514959/1125899906842624)), (352147/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227472754315145/2251799813685248), (-16561879152283/2251799813685248)), (4137/17592186044416), by norm_num⟩
  | 0 => ⟨((34425616334155/35184372088832), (-32884098284733/2251799813685248)), (532175/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((34425616334155/35184372088832), (-32884098284733/2251799813685248)), (2030086521628951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2155246065964381/2251799813685248), (-32174948246531/1125899906842624)), (1056941/1125899906842624), by norm_num⟩
  | 2 => ⟨((2060993462860715/2251799813685248), (-30795335451003/562949953421312)), (2083651/1125899906842624), by norm_num⟩
  | 3 => ⟨((1879616644989019/2251799813685248), (-225487131370699/2251799813685248)), (505269/140737488355328), by norm_num⟩
  | 4 => ⟨((386592345436697/562949953421312), (-376436095943681/2251799813685248)), (15115287/2251799813685248), by norm_num⟩
  | 5 => ⟨((249750679079355/562949953421312), (-517016876379377/2251799813685248)), (25813803/2251799813685248), by norm_num⟩
  | 6 => ⟨((648991950623397/4503599627370496), (-28671579770653/140737488355328)), (8689545/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1086193115/33554432)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1209240061/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-172913079487721/9007199254740992), (1912788833598283/9007199254740992)), (39277455/2251799813685248), by norm_num⟩
  | 1 => ⟨((147733043/4294967296), (-817121865/2147483648)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((-132351039/4294967296), (1464085839/4294967296)), (125/4294967296), by norm_num⟩
  | 3 => ⟨((19761769/1073741824), (-874429889/4294967296)), (19/1073741824), by norm_num⟩
  | 4 => ⟨((-141633347/17179869184), (783384017/8589934592)), (69/8589934592), by norm_num⟩
  | 5 => ⟨((25377289/8589934592), (-1122908585/34359738368)), (101/34359738368), by norm_num⟩
  | 6 => ⟨((-7578333/8589934592), (670660697/68719476736)), (61/68719476736), by norm_num⟩
  | 7 => ⟨((62073371/274877906944), (-343332187/137438953472)), (127/549755813888), by norm_num⟩
  | 8 => ⟨((-55610275/1099511627776), (1230337395/2199023255552)), (29/549755813888), by norm_num⟩
  | 9 => ⟨((177138199/17592186044416), (-979763857/8796093022208)), (187/17592186044416), by norm_num⟩
  | 10 => ⟨((-63477809/35184372088832), (1404400935/70368744177664)), (17/8796093022208), by norm_num⟩
  | 11 => ⟨((82717793/281474976710656), (-1830071763/562949953421312)), (179/562949953421312), by norm_num⟩
  | 12 => ⟨((-49403463/1125899906842624), (1093016137/2251799813685248)), (27/562949953421312), by norm_num⟩
  | 13 => ⟨((108946613/18014398509481984), (-602591389/9007199254740992)), (121/18014398509481984), by norm_num⟩
  | 14 => ⟨((-111546357/144115188075855872), (1233941517/144115188075855872)), (63/72057594037927936), by norm_num⟩
  | 15 => ⟨((53297131/576460752303423488), (-589580373/576460752303423488)), (61/576460752303423488), by norm_num⟩
  | 16 => ⟨((-95495639/9223372036854775808), (132048277/1152921504606846976)), (111/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (2163572431601/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((13902982610537/4951760157141521099596496896), (2562711854905/633825300114114700748351602688)), (23113/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945328090819303/19807040628566084398385987584), (2882651777301/39614081257132168796771975168)), (52013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890488032258547/2475880078570760549798248448), (3062333975683/2475880078570760549798248448)), (55273/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772153867444233/154742504910672534362390528), (1530895031205/77371252455336267181195264)), (13821/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550455966609399/9671406556917033397649408), (358731295019/1208925819614629174706176)), (405/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1259577967304075/604462909807314587353088), (2510541336785/604462909807314587353088)), (45371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889073806510253/75557863725914323419136), (1019636658383/18889465931478580854784)), (73749/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((5072265832271/18446744073709551616), (1528981259087/2361183241434822606848)), (27665/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202845970900845/73786976294838206464), (4203159223553/590295810358705651712)), (19027/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912561213200397/36893488147419103232), (5251640833743/73786976294838206464)), (23795/18446744073709551616), by norm_num⟩
  | 7 => ⟨((114031765559157/576460752303423488), (738115405739/1152921504606846976)), (107139/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595753716682937/1152921504606846976), (184404968645/36028797018963968)), (6701/72057594037927936), by norm_num⟩
  | 5 => ⟨((598062111360567/72057594037927936), (5158881563723/144115188075855872)), (93901/144115188075855872), by norm_num⟩
  | 4 => ⟨((746972886924031/18014398509481984), (3864706392647/18014398509481984)), (141025/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492131239756877/9007199254740992), (9646186756097/9007199254740992)), (176585/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116829788396445/2251799813685248), (1202855366945/281474976710656)), (177043/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112291129616283/1125899906842624), (14375992448695/1125899906842624)), (266709/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098668590939499/1125899906842624), (3564927866553/140737488355328)), (67251/140737488355328), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098668590939499/1125899906842624), (3564927866553/140737488355328)), (256542206347417787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1071373492351833/1125899906842624), (6957411137781/140737488355328)), (263/274877906944), by norm_num⟩
  | 2 => ⟨((508368104790511/562949953421312), (211855020450343/2251799813685248)), (4313329/2251799813685248), by norm_num⟩
  | 3 => ⟨((1816381502896079/2251799813685248), (382628454206809/2251799813685248)), (8601863/2251799813685248), by norm_num⟩
  | 4 => ⟨((700070497149225/1125899906842624), (617283332629419/2251799813685248)), (16800413/2251799813685248), by norm_num⟩
  | 5 => ⟨((87671874825111/281474976710656), (767638130049533/2251799813685248)), (30103531/2251799813685248), by norm_num⟩
  | 6 => ⟨((-172913079487721/9007199254740992), (1912788833598283/9007199254740992)), (39277455/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1209240061/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-1313274771/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((110047556905591/4503599627370496), (-833508584602599/4503599627370496)), (64428707/2251799813685248), by norm_num⟩
  | 1 => ⟨((-204222353/4294967296), (386698917/1073741824)), (241/4294967296), by norm_num⟩
  | 2 => ⟨((198699175/4294967296), (-1504962695/4294967296)), (237/4294967296), by norm_num⟩
  | 3 => ⟨((-32220895/1073741824), (976174061/4294967296)), (155/4294967296), by norm_num⟩
  | 4 => ⟨((125397933/8589934592), (-474886753/4294967296)), (19/1073741824), by norm_num⟩
  | 5 => ⟨((-24401311/4294967296), (369634781/8589934592)), (119/17179869184), by norm_num⟩
  | 6 => ⟨((63310345/34359738368), (-479517381/34359738368)), (39/17179869184), by norm_num⟩
  | 7 => ⟨((-70397853/137438953472), (1066397415/274877906944)), (175/274877906944), by norm_num⟩
  | 8 => ⟨((136987897/1099511627776), (-129694597/137438953472)), (43/274877906944), by norm_num⟩
  | 9 => ⟨((-236947679/8796093022208), (1794659787/8796093022208)), (75/2199023255552), by norm_num⟩
  | 10 => ⟨((184431557/35184372088832), (-698449339/17592186044416)), (59/8796093022208), by norm_num⟩
  | 11 => ⟨((-65252225/70368744177664), (247112665/35184372088832)), (21/17592186044416), by norm_num⟩
  | 12 => ⟨((42324989/281474976710656), (-1282290781/1125899906842624)), (219/1125899906842624), by norm_num⟩
  | 13 => ⟨((-25341731/1125899906842624), (383880407/2251799813685248)), (33/1125899906842624), by norm_num⟩
  | 14 => ⟨((112714815/36028797018963968), (-426855303/18014398509481984)), (295/72057594037927936), by norm_num⟩
  | 15 => ⟨((-29244387/72057594037927936), (885996871/288230376151711744)), (77/144115188075855872), by norm_num⟩
  | 16 => ⟨((113813899/2305843009213693952), (-1724070303/4611686018427387904)), (151/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-937571842633/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889688765567855/316912650057057350374175801344), (-1110293181571/316912650057057350374175801344)), (92419/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890426492692281/39614081257132168796771975168), (-2497786892031/39614081257132168796771975168)), (103985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890244092512353/2475880078570760549798248448), (-165840236547/154742504910672534362390528)), (27625/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885955022757709/77371252455336267181195264), (-165808265343/9671406556917033397649408)), (110519/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550227508693077/9671406556917033397649408), (-2486580575311/9671406556917033397649408)), (103631/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259378191725357/604462909807314587353088), (-1087607358683/302231454903657293676544)), (11337/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944374702830241/37778931862957161709568), (-3533705506837/75557863725914323419136)), (73709/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298256957488277/4722366482869645213696), (-331173534343/590295810358705651712)), (110595/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405608460962097/147573952589676412928), (-3641461710933/590295810358705651712)), (19015/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912352760739539/36893488147419103232), (-2274828608143/36893488147419103232)), (190227/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824039916917773/9223372036854775808), (-5115382070077/9223372036854775808)), (214113/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398821560354923/288230376151711744), (-5111656214331/1152921504606846976)), (214247/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37366129521979/4503599627370496), (-4468510372499/144115188075855872)), (187617/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493335579938427/36028797018963968), (-3347197428997/18014398509481984)), (140863/18014398509481984), by norm_num⟩
  | 3 => ⟨((745685928536171/4503599627370496), (-4176680215331/4503599627370496)), (352685/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232150867537439/4503599627370496), (-4165720935325/1125899906842624)), (706955/4503599627370496), by norm_num⟩
  | 1 => ⟨((277793031903137/281474976710656), (-3110618841809/281474976710656)), (1064407/2251799813685248), by norm_num⟩
  | 0 => ⟨((2192960931481247/2251799813685248), (-24666854159699/1125899906842624)), (2144751/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2192960931481247/2251799813685248), (-24666854159699/1125899906842624)), (8181575783736418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266822332685521/281474976710656), (-48044632694269/1125899906842624)), (1067849/562949953421312), by norm_num⟩
  | 2 => ⟨((2019359308720607/2251799813685248), (-182174360482235/2251799813685248)), (264457/70368744177664), by norm_num⟩
  | 3 => ⟨((449043526817789/562949953421312), (-326739071931947/2251799813685248)), (16547433/2251799813685248), by norm_num⟩
  | 4 => ⟨((1385328741722873/2251799813685248), (-260627191312133/1125899906842624)), (31200611/2251799813685248), by norm_num⟩
  | 5 => ⟨((731605705456705/2251799813685248), (-160340336119093/562949953421312)), (52834679/2251799813685248), by norm_num⟩
  | 6 => ⟨((110047556905591/4503599627370496), (-833508584602599/4503599627370496)), (64428707/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1313274771/33554432)), (1/16777216), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-1403393737/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-830137018265635/9007199254740992), (77976357676839/562949953421312)), (134364229/4503599627370496), by norm_num⟩
  | 1 => ⟨((823126507/4294967296), (-77317847/268435456)), (269/4294967296), by norm_num⟩
  | 2 => ⟨((-427910863/2147483648), (160777943/536870912)), (283/4294967296), by norm_num⟩
  | 3 => ⟨((37075651/268435456), (-891542223/4294967296)), (199/4294967296), by norm_num⟩
  | 4 => ⟨((-616773191/8589934592), (926954967/8589934592)), (209/8589934592), by norm_num⟩
  | 5 => ⟨((256508759/8589934592), (-385509733/8589934592)), (11/1073741824), by norm_num⟩
  | 6 => ⟨((-177798323/17179869184), (534429969/34359738368)), (247/68719476736), by norm_num⟩
  | 7 => ⟨((52817317/17179869184), (-635037645/137438953472)), (37/34359738368), by norm_num⟩
  | 8 => ⟨((-109830523/137438953472), (330130915/274877906944)), (39/137438953472), by norm_num⟩
  | 9 => ⟨((203009913/1099511627776), (-610211501/2199023255552)), (291/4398046511104), by norm_num⟩
  | 10 => ⟨((-337717797/8796093022208), (253779829/4398046511104)), (245/17592186044416), by norm_num⟩
  | 11 => ⟨((510737757/70368744177664), (-767593191/70368744177664)), (187/70368744177664), by norm_num⟩
  | 12 => ⟨((-708032873/562949953421312), (33253441/17592186044416)), (131/281474976710656), by norm_num⟩
  | 13 => ⟨((453019375/2251799813685248), (-340423811/1125899906842624)), (169/2251799813685248), by norm_num⟩
  | 14 => ⟨((-538301319/18014398509481984), (809018759/18014398509481984)), (203/18014398509481984), by norm_num⟩
  | 15 => ⟨((596995267/144115188075855872), (-897230515/144115188075855872)), (227/144115188075855872), by norm_num⟩
  | 16 => ⟨((-620708379/1152921504606846976), (932869203/1152921504606846976)), (119/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (175681976563/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779196600163875/633825300114114700748351602688), (3328111028259/633825300114114700748351602688)), (5783/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((59069462141959/1237940039285380274899124224), (467940360641/4951760157141521099596496896)), (104115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890027452679775/2475880078570760549798248448), (1988381984443/1237940039285380274899124224)), (55323/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221461647019895/19342813113834066795298816), (1987971907143/77371252455336267181195264)), (55337/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48438248436193/302231454903657293676544), (3726576036613/9671406556917033397649408)), (103785/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259199834293791/604462909807314587353088), (3259882883211/604462909807314587353088)), (45421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944229559285463/37778931862957161709568), (1323919144933/18889465931478580854784)), (147671/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298038843312067/4722366482869645213696), (1985164383081/2361183241434822606848)), (55401/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811066644703005/295147905179352825856), (2728440513575/295147905179352825856)), (76215/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824328858468011/73786976294838206464), (426101295329/4611686018427387904)), (95327/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911807419657153/4611686018427387904), (7665039142379/9223372036854775808)), (107323/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199357437766679/144115188075855872), (1914765329707/288230376151711744)), (214847/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195340882504005/144115188075855872), (6694956895687/144115188075855872)), (188217/144115188075855872), by norm_num⟩
  | 4 => ⟨((746384483076847/18014398509481984), (10029000066895/36028797018963968)), (282777/36028797018963968), by norm_num⟩
  | 3 => ⟨((745328550912331/4503599627370496), (6256378454167/4503599627370496)), (354263/9007199254740992), by norm_num⟩
  | 2 => ⟨((139418874010603/281474976710656), (6238777155131/1125899906842624)), (355453/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110061408207985/1125899906842624), (18628455258485/1125899906842624)), (16755/35184372088832), by norm_num⟩
  | 0 => ⟨((1094163751892737/1125899906842624), (36906189098049/1125899906842624)), (542139/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094163751892737/1125899906842624), (36906189098049/1125899906842624)), (2068096163036155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((531056198643687/562949953421312), (71731801532565/1125899906842624)), (2178515/1125899906842624), by norm_num⟩
  | 2 => ⟨((249342167606509/281474976710656), (1057310290535/8796093022208)), (2193887/562949953421312), by norm_num⟩
  | 3 => ⟨((1734485459082575/2251799813685248), (119885971650849/562949953421312)), (1103573/140737488355328), by norm_num⟩
  | 4 => ⟨((154236482951553/281474976710656), (738752968403785/2251799813685248)), (34721993/2251799813685248), by norm_num⟩
  | 5 => ⟨((108439166841949/562949953421312), (809611290837747/2251799813685248)), (15208759/562949953421312), by norm_num⟩
  | 6 => ⟨((-830137018265635/9007199254740992), (77976357676839/562949953421312)), (134364229/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1403393737/33554432)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile013Terms0

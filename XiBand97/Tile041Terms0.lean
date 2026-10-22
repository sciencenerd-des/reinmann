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
namespace Reinmann.XiBand97.Tile041Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35053/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35053/1280))
  have he : value ((69/80), (35053/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-79616043/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1227649504118451/2251799813685248), (-81741090446713/1125899906842624)), (10572897/562949953421312), by norm_num⟩
  | 1 => ⟨((-1623042665/4294967296), (216135431/4294967296)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((1125007447/8589934592), (-149813665/8589934592)), (21/4294967296), by norm_num⟩
  | 3 => ⟨((-1039727653/34359738368), (69228613/17179869184)), (41/34359738368), by norm_num⟩
  | 4 => ⟨((1441368583/274877906944), (-23992809/34359738368)), (59/274877906944), by norm_num⟩
  | 5 => ⟨((-1598528911/2199023255552), (212871013/2199023255552)), (17/549755813888), by norm_num⟩
  | 6 => ⟨((738677205/8796093022208), (-98367295/8796093022208)), (65/17592186044416), by norm_num⟩
  | 7 => ⟨((-1170313193/140737488355328), (155846887/140737488355328)), (53/140737488355328), by norm_num⟩
  | 8 => ⟨((405599645/562949953421312), (-216049661/2251799813685248)), (19/562949953421312), by norm_num⟩
  | 9 => ⟨((-999609779/18014398509481984), (16639357/2251799813685248)), (49/18014398509481984), by norm_num⟩
  | 10 => ⟨((34643835/9007199254740992), (-147629099/288230376151711744)), (7/36028797018963968), by norm_num⟩
  | 11 => ⟨((-139713609/576460752303423488), (18605217/576460752303423488)), (59/4611686018427387904), by norm_num⟩
  | 12 => ⟨((516491169/36893488147419103232), (-137558973/73786976294838206464)), (7/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-440620797/590295810358705651712), (234704281/2361183241434822606848)), (49/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((698091573/18889465931478580854784), (-185925269/37778931862957161709568)), (5/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-258069443/151115727451828646838272), (34366287/151115727451828646838272)), (61/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1431040855/19342813113834066795298816), (-23820895/2417851639229258349412352)), (87/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-21556256559/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781048401612139/633825300114114700748351602688), (-51145768779/158456325028528675187087900672)), (46111/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892306182485295/39614081257132168796771975168), (-230143547827/39614081257132168796771975168)), (51875/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892241223819423/2475880078570760549798248448), (-61128149067/618970019642690137449562112)), (27559/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443476783188499/38685626227668133590597632), (-244495809035/154742504910672534362390528)), (55119/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552099731089305/9671406556917033397649408), (-229196986141/9671406556917033397649408)), (51675/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630508169678271/302231454903657293676544), (-200529529851/604462909807314587353088)), (45217/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945705653670157/37778931862957161709568), (-325827052929/75557863725914323419136)), (36739/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300253306394517/4722366482869645213696), (-30542629949/590295810358705651712)), (27555/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625178697594301/590295810358705651712), (-167960702607/295147905179352825856)), (37889/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828136399135779/73786976294838206464), (-419830482771/73786976294838206464)), (94727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827899392830757/9223372036854775808), (-118052828043/2305843009213693952)), (26643/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599145389241201/1152921504606846976), (-236044433333/576460752303423488)), (53289/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199092528189467/144115188075855872), (-103235012327/36028797018963968)), (93263/144115188075855872), by norm_num⟩
  | 4 => ⟨((374599852268163/9007199254740992), (-619134761301/36028797018963968)), (34977/9007199254740992), by norm_num⟩
  | 3 => ⟨((748850163994911/4503599627370496), (-773436891495/9007199254740992)), (174909/9007199254740992), by norm_num⟩
  | 2 => ⟨((2244803823635403/4503599627370496), (-1545430050231/4503599627370496)), (349889/4503599627370496), by norm_num⟩
  | 1 => ⟨((2241313588153581/2251799813685248), (-1157269529011/1125899906842624)), (65627/281474976710656), by norm_num⟩
  | 0 => ⟨((2230858374804693/2251799813685248), (-2307336958547/1125899906842624)), (525381/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2230858374804693/2251799813685248), (-2307336958547/1125899906842624)), (2004169468406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2210102231546107/2251799813685248), (-9143516126413/2251799813685248)), (130393/140737488355328), by norm_num⟩
  | 2 => ⟨((1084569827280541/1125899906842624), (-8974201557505/1125899906842624)), (2056127/1125899906842624), by norm_num⟩
  | 3 => ⟨((1044685381715869/1125899906842624), (-34579088865897/2251799813685248)), (7988155/2251799813685248), by norm_num⟩
  | 4 => ⟨((1938127202592689/2251799813685248), (-4010599480437/140737488355328)), (15069227/2251799813685248), by norm_num⟩
  | 5 => ⟨((833160055820345/1125899906842624), (-110461711979881/2251799813685248)), (13399533/1125899906842624), by norm_num⟩
  | 6 => ⟨((1227649504118451/2251799813685248), (-81741090446713/1125899906842624)), (10572897/562949953421312), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-79616043/4194304)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1009507541/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((415941331492243/4503599627370496), (1695726126114317/4503599627370496)), (63561123/2251799813685248), by norm_num⟩
  | 1 => ⟨((-217894677/2147483648), (-888321667/2147483648)), (17/536870912), by norm_num⟩
  | 2 => ⟨((119690885/2147483648), (243980275/1073741824)), (19/1073741824), by norm_num⟩
  | 3 => ⟨((-350650339/17179869184), (-714772609/8589934592)), (113/17179869184), by norm_num⟩
  | 4 => ⟨((96307193/17179869184), (196314493/8589934592)), (127/68719476736), by norm_num⟩
  | 5 => ⟨((-169286825/137438953472), (-1380310493/274877906944)), (57/137438953472), by norm_num⟩
  | 6 => ⟨((247974115/1099511627776), (1010950713/1099511627776)), (43/549755813888), by norm_num⟩
  | 7 => ⟨((-77836403/2199023255552), (-1269306145/8796093022208)), (55/4398046511104), by norm_num⟩
  | 8 => ⟨((342048115/70368744177664), (1394475329/70368744177664)), (31/17592186044416), by norm_num⟩
  | 9 => ⟨((-167012561/281474976710656), (-680883437/281474976710656)), (123/562949953421312), by norm_num⟩
  | 10 => ⟨((293571283/4503599627370496), (598421529/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | 11 => ⟨((-234560741/36028797018963968), (-956266539/36028797018963968)), (45/18014398509481984), by norm_num⟩
  | 12 => ⟨((343588417/576460752303423488), (1400754895/576460752303423488)), (67/288230376151711744), by norm_num⟩
  | 13 => ⟨((-29036189/576460752303423488), (-473503551/2305843009213693952)), (93/4611686018427387904), by norm_num⟩
  | 14 => ⟨((72913175/18446744073709551616), (1189021303/73786976294838206464)), (119/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-341774123/1180591620717411303424), (-696679155/590295810358705651712)), (71/590295810358705651712), by norm_num⟩
  | 16 => ⟨((93869313/4722366482869645213696), (765380281/9444732965739290427392)), (159/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (866404358719/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780505905309669/633825300114114700748351602688), (256812932601/79228162514264337593543950336)), (23101/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891695783234105/39614081257132168796771975168), (2311117489631/39614081257132168796771975168)), (51983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236449070111781/309485009821345068724781056), (1227662258739/1237940039285380274899124224)), (6905/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773258341941737/154742504910672534362390528), (306882122779/19342813113834066795298816)), (3453/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1551491353872893/9671406556917033397649408), (2301331678945/9671406556917033397649408)), (12951/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((39390121047457/18889465931478580854784), (125836312079/37778931862957161709568)), (22669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472636448974505/18889465931478580854784), (3271211224853/75557863725914323419136)), (36845/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299603950283795/4722366482869645213696), (2452942174807/4722366482869645213696)), (55283/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624285471556843/590295810358705651712), (3372037908333/590295810358705651712)), (76037/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827019324903737/73786976294838206464), (4213911124819/73786976294838206464)), (47541/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826641940140299/9223372036854775808), (4739087839985/9223372036854775808)), (13377/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1597887007282755/1152921504606846976), (4737135395303/1152921504606846976)), (53539/576460752303423488), by norm_num⟩
  | 5 => ⟨((299497599965901/36028797018963968), (2071398674341/72057594037927936)), (46881/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496744131643237/36028797018963968), (3104902362579/18014398509481984)), (70391/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495627589940525/9007199254740992), (3877286634381/4503599627370496)), (176221/9007199254740992), by norm_num⟩
  | 2 => ⟨((560161863314551/1125899906842624), (7743053588989/2251799813685248)), (88293/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117525950029537/1125899906842624), (2896449048945/281474976710656)), (4153/17592186044416), by norm_num⟩
  | 0 => ⟨((1109113543299305/1125899906842624), (23056546055041/1125899906842624)), (133811/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109113543299305/1125899906842624), (23056546055041/1125899906842624)), (510448456884288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1092105292967061/1125899906842624), (45425578838643/1125899906842624)), (1076451/1125899906842624), by norm_num⟩
  | 2 => ⟨((132186538128059/140737488355328), (44062100710973/562949953421312)), (271893/140737488355328), by norm_num⟩
  | 3 => ⟨((493171770225993/562949953421312), (165539874945847/1125899906842624)), (4426471/1125899906842624), by norm_num⟩
  | 4 => ⟨((839746165576713/1125899906842624), (72510524846721/281474976710656)), (9057251/1125899906842624), by norm_num⟩
  | 5 => ⟨((1103204999680047/2251799813685248), (216326282057327/562949953421312)), (9088531/562949953421312), by norm_num⟩
  | 6 => ⟨((415941331492243/4503599627370496), (1695726126114317/4503599627370496)), (63561123/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1009507541/33554432)), (1/33554432), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-79616043/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((657428281366545/2251799813685248), (-178256359278735/2251799813685248)), (105494063/4503599627370496), by norm_num⟩
  | 1 => ⟨((-869168395/2147483648), (117833989/1073741824)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((1204923245/4294967296), (-326705189/4294967296)), (25/1073741824), by norm_num⟩
  | 3 => ⟨((-1113585533/8589934592), (75484927/2147483648)), (95/8589934592), by norm_num⟩
  | 4 => ⟨((1543757345/34359738368), (-418577315/34359738368)), (67/17179869184), by norm_num⟩
  | 5 => ⟨((-856040841/68719476736), (232108549/68719476736)), (19/17179869184), by norm_num⟩
  | 6 => ⟨((791149727/274877906944), (-429027697/549755813888)), (143/549755813888), by norm_num⟩
  | 7 => ⟨((-156680915/274877906944), (339862101/2199023255552)), (29/549755813888), by norm_num⟩
  | 8 => ⟨((217205869/2199023255552), (-235574457/8796093022208)), (41/4398046511104), by norm_num⟩
  | 9 => ⟨((-535308927/35184372088832), (145144685/35184372088832)), (103/70368744177664), by norm_num⟩
  | 10 => ⟨((1187353195/562949953421312), (-321941213/562949953421312)), (29/140737488355328), by norm_num⟩
  | 11 => ⟨((-598553105/2251799813685248), (5071651/70368744177664)), (119/4503599627370496), by norm_num⟩
  | 12 => ⟨((1106361059/36028797018963968), (-149990425/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 13 => ⟨((-943841291/288230376151711744), (127957465/144115188075855872)), (97/288230376151711744), by norm_num⟩
  | 14 => ⟨((1495362125/4611686018427387904), (-202727671/2305843009213693952)), (39/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-276401611/9223372036854775808), (149888121/18446744073709551616)), (117/36893488147419103232), by norm_num⟩
  | 16 => ⟨((1532695979/590295810358705651712), (-207789057/295147905179352825856)), (41/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-21556256559/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780124929954811/633825300114114700748351602688), (-408763425843/633825300114114700748351602688)), (92241/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891267356353943/39614081257132168796771975168), (-459809901195/39614081257132168796771975168)), (103773/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945568783563263/1237940039285380274899124224), (-122122102997/618970019642690137449562112)), (55131/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443200896031949/38685626227668133590597632), (-488421365755/154742504910672534362390528)), (110265/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775532634529223/4835703278458516698824704), (-457823806595/9671406556917033397649408)), (103377/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630055649934625/302231454903657293676544), (-100131155349/151115727451828646838272)), (90459/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472485208342281/18889465931478580854784), (-162679755709/18889465931478580854784)), (73501/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649575319588645/2361183241434822606848), (-121980624175/1180591620717411303424)), (110257/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623662836029323/590295810358705651712), (-670703738447/590295810358705651712)), (151613/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57070063464147/2305843009213693952), (-104761903969/9223372036854775808)), (189531/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825768859001185/9223372036854775808), (-235616548029/2305843009213693952)), (106621/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597015643242793/1152921504606846976), (-941977757287/1152921504606846976)), (106633/576460752303423488), by norm_num⟩
  | 5 => ⟨((299307471591535/36028797018963968), (-411840692345/72057594037927936)), (46659/36028797018963968), by norm_num⟩
  | 4 => ⟨((373901804306677/9007199254740992), (-1234424611223/36028797018963968)), (140005/18014398509481984), by norm_num⟩
  | 3 => ⟨((747106592538009/4503599627370496), (-1541112087485/9007199254740992)), (350109/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237838819845841/4503599627370496), (-1538237846131/2251799813685248)), (350255/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230889257341361/2251799813685248), (-575046088977/281474976710656)), (1051501/2251799813685248), by norm_num⟩
  | 0 => ⟨((2210102231546107/2251799813685248), (-4571758063207/1125899906842624)), (1052979/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210102231546107/2251799813685248), (-4571758063207/1125899906842624)), (4016796116355514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1084569827280541/1125899906842624), (-4487100778753/562949953421312)), (2075513/1125899906842624), by norm_num⟩
  | 2 => ⟨((1044685381715869/1125899906842624), (-8644772216475/562949953421312)), (8063471/2251799813685248), by norm_num⟩
  | 3 => ⟨((1938127202592689/2251799813685248), (-64169591686997/2251799813685248)), (15211307/2251799813685248), by norm_num⟩
  | 4 => ⟨((1666320111640689/2251799813685248), (-55230855989945/1125899906842624)), (27051741/2251799813685248), by norm_num⟩
  | 5 => ⟨((1227649504118449/2251799813685248), (-163482180893439/2251799813685248)), (21345167/1125899906842624), by norm_num⟩
  | 6 => ⟨((657428281366545/2251799813685248), (-178256359278735/2251799813685248)), (105494063/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-79616043/2097152)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-184862727/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1119028338663439/4503599627370496), (-25926631414599/1125899906842624)), (4679953/281474976710656), by norm_num⟩
  | 1 => ⟨((-858786885/2147483648), (159177031/4294967296)), (117/4294967296), by norm_num⟩
  | 2 => ⟨((345541043/1073741824), (-64046387/2147483648)), (3/134217728), by norm_num⟩
  | 3 => ⟨((-1483004947/8589934592), (137438245/8589934592)), (105/8589934592), by norm_num⟩
  | 4 => ⟨((1193402193/17179869184), (-110599161/17179869184)), (43/8589934592), by norm_num⟩
  | 5 => ⟨((-384141347/17179869184), (71200993/34359738368)), (113/68719476736), by norm_num⟩
  | 6 => ⟨((1648671061/274877906944), (-152791437/274877906944)), (31/68719476736), by norm_num⟩
  | 7 => ⟨((-1516247835/1099511627776), (140519047/1099511627776)), (29/274877906944), by norm_num⟩
  | 8 => ⟨((1220153375/4398046511104), (-113078341/4398046511104)), (95/4398046511104), by norm_num⟩
  | 9 => ⟨((-1745565423/35184372088832), (161771173/35184372088832)), (69/17592186044416), by norm_num⟩
  | 10 => ⟨((280937917/35184372088832), (-13018033/17592186044416)), (91/140737488355328), by norm_num⟩
  | 11 => ⟨((-1315351665/1125899906842624), (30475223/281474976710656)), (27/281474976710656), by norm_num⟩
  | 12 => ⟨((352829473/2251799813685248), (-130794611/9007199254740992)), (59/4503599627370496), by norm_num⟩
  | 13 => ⟨((-174725271/9007199254740992), (64771017/36028797018963968)), (119/72057594037927936), by norm_num⟩
  | 14 => ⟨((1285529031/576460752303423488), (-119137063/576460752303423488)), (111/576460752303423488), by norm_num⟩
  | 15 => ⟨((-17241493/72057594037927936), (51131655/2305843009213693952)), (97/4611686018427387904), by norm_num⟩
  | 16 => ⟨((55498225/2305843009213693952), (-10286653/4611686018427387904)), (79/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-60188180789/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827931822525/633825300114114700748351602688), (-71310281809/316912650057057350374175801344)), (46107/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59091664888097/1237940039285380274899124224), (-160428398865/39614081257132168796771975168)), (51871/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890782659777411/2475880078570760549798248448), (-170431032973/2475880078570760549798248448)), (110227/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772448735919105/154742504910672534362390528), (-170403880849/154742504910672534362390528)), (110229/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550732661685949/9671406556917033397649408), (-159724795281/9671406556917033397649408)), (25835/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629910165613111/302231454903657293676544), (-139730359739/604462909807314587353088)), (11303/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889468127056643/75557863725914323419136), (-56751945363/18889465931478580854784)), (146941/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298796212426439/4722366482869645213696), (-85104277111/2361183241434822606848)), (110209/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623175666534429/590295810358705651712), (-233959956421/590295810358705651712)), (151539/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912816659904613/36893488147419103232), (-292334785001/73786976294838206464)), (189429/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228135550473679/1152921504606846976), (-5136224457/144115188075855872)), (213115/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399082904665693/288230376151711744), (-328520647103/1152921504606846976)), (213123/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598315924482079/72057594037927936), (-287233293661/144115188075855872)), (186493/144115188075855872), by norm_num⟩
  | 4 => ⟨((747355564223797/18014398509481984), (-3362545281/281474976710656)), (279759/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493094764924553/9007199254740992), (-268615446247/4503599627370496)), (174867/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235607044042413/4503599627370496), (-1072136325071/4503599627370496)), (699573/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227554227040523/2251799813685248), (-400600852391/562949953421312)), (262407/562949953421312), by norm_num⟩
  | 0 => ⟨((550870634459157/562949953421312), (-1590838891143/1125899906842624)), (2100347/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550870634459157/562949953421312), (-1590838891143/1125899906842624)), (8012187966353606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2156197518966535/2251799813685248), (-3113407946693/1125899906842624)), (257281/140737488355328), by norm_num⟩
  | 2 => ⟨((2064636891479519/2251799813685248), (-11924901049181/2251799813685248)), (1976555/562949953421312), by norm_num⟩
  | 3 => ⟨((1892967245350787/2251799813685248), (-21867477280841/2251799813685248)), (1822737/281474976710656), by norm_num⟩
  | 4 => ⟨((1591103606827601/2251799813685248), (-36765628968891/2251799813685248)), (24799649/2251799813685248), by norm_num⟩
  | 5 => ⟨((1123660709450613/2251799813685248), (-25978297228807/1125899906842624)), (8964071/562949953421312), by norm_num⟩
  | 6 => ⟨((1119028338663439/4503599627370496), (-25926631414599/1125899906842624)), (4679953/281474976710656), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-184862727/4194304)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1646435885/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((87469051406773/1125899906842624), (894288350860619/4503599627370496)), (66871529/4503599627370496), by norm_num⟩
  | 1 => ⟨((-597852711/4294967296), (-11938435/33554432)), (117/4294967296), by norm_num⟩
  | 2 => ⟨((16737629/134217728), (684505727/2147483648)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((-39986407/536870912), (-204411603/1073741824)), (65/4294967296), by norm_num⟩
  | 4 => ⟨((573168187/17179869184), (1465025701/17179869184)), (119/17179869184), by norm_num⟩
  | 5 => ⟨((-410791811/34359738368), (-1049989469/34359738368)), (87/34359738368), by norm_num⟩
  | 6 => ⟨((122673353/34359738368), (1254219049/137438953472)), (53/68719476736), by norm_num⟩
  | 7 => ⟨((-251201305/274877906944), (-1284147919/549755813888)), (55/274877906944), by norm_num⟩
  | 8 => ⟨((450092317/2199023255552), (1150442097/2199023255552)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((-358425409/8796093022208), (-114517529/1099511627776)), (81/8796093022208), by norm_num⟩
  | 10 => ⟨((513769697/70368744177664), (1313202349/70368744177664)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-10460815/8796093022208), (-855615543/281474976710656)), (39/140737488355328), by norm_num⟩
  | 12 => ⟨((199928153/1125899906842624), (127754771/281474976710656)), (95/2251799813685248), by norm_num⟩
  | 13 => ⟨((-440890045/18014398509481984), (-281730241/4503599627370496)), (107/18014398509481984), by norm_num⟩
  | 14 => ⟨((56426351/18014398509481984), (72113261/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 15 => ⟨((-26960653/72057594037927936), (-1102588743/1152921504606846976)), (109/1152921504606846976), by norm_num⟩
  | 16 => ⟨((386456043/9223372036854775808), (987786911/9223372036854775808)), (25/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (780179332483/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889791729105155/316912650057057350374175801344), (231027026771/79228162514264337593543950336)), (2887/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945329086918553/19807040628566084398385987584), (519739352765/9903520314283042199192993792)), (12993/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((59077821031925/77371252455336267181195264), (2208543758405/2475880078570760549798248448)), (27613/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443039061922779/38685626227668133590597632), (1104075890419/77371252455336267181195264)), (27617/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775229173111035/4835703278458516698824704), (1034862948639/4835703278458516698824704)), (25895/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157447524689657/75557863725914323419136), (452648462903/151115727451828646838272)), (11331/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236134713504533/9444732965739290427392), (2941434618987/75557863725914323419136)), (73667/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298503221788755/4722366482869645213696), (1102696655813/2361183241434822606848)), (55263/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405693129522291/147573952589676412928), (1515653423209/295147905179352825856)), (9501/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1825128955276375/73786976294838206464), (3787470740779/73786976294838206464)), (95043/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912258202330883/4611686018427387904), (2129309607115/4611686018427387904)), (106967/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595762884470011/1152921504606846976), (4255764009175/1152921504606846976)), (107023/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196133381273239/144115188075855872), (232536467053/9007199254740992)), (23427/36028797018963968), by norm_num⟩
  | 4 => ⟨((186745222568927/4503599627370496), (87100942389/562949953421312)), (70343/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492155208325869/9007199254740992), (3478430478817/4503599627370496)), (176077/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233719353192473/4503599627370496), (13880125124053/4503599627370496)), (176407/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224701377675787/2251799813685248), (20736358348803/2251799813685248)), (530873/2251799813685248), by norm_num⟩
  | 0 => ⟨((549423092604031/562949953421312), (41138374059811/2251799813685248)), (534185/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549423092604031/562949953421312), (41138374059811/2251799813685248)), (2037754063132857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2144133488164427/2251799813685248), (80299758666921/2251799813685248)), (2124435/2251799813685248), by norm_num⟩
  | 2 => ⟨((1019375775751771/1125899906842624), (152920699791241/2251799813685248)), (2098617/1125899906842624), by norm_num⟩
  | 3 => ⟨((229434424144551/281474976710656), (69226250055987/562949953421312)), (510645/140737488355328), by norm_num⟩
  | 4 => ⟨((1462072036654781/2251799813685248), (225709368596683/1125899906842624)), (3832229/562949953421312), by norm_num⟩
  | 5 => ⟨((429406680008927/1125899906842624), (586203718875241/2251799813685248)), (26051819/2251799813685248), by norm_num⟩
  | 6 => ⟨((87469051406773/1125899906842624), (894288350860619/4503599627370496)), (66871529/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1646435885/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-894041961/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-26090417288357/140737488355328), (-197991051553307/9007199254740992)), (139530483/4503599627370496), by norm_num⟩
  | 1 => ⟨((48417671/134217728), (91856193/2147483648)), (261/4294967296), by norm_num⟩
  | 2 => ⟨((-753731499/2147483648), (-89371949/2147483648)), (1/16777216), by norm_num⟩
  | 3 => ⟨((977795849/4294967296), (115939855/4294967296)), (167/4294967296), by norm_num⟩
  | 4 => ⟨((-951351433/8589934592), (-225608541/17179869184)), (327/17179869184), by norm_num⟩
  | 5 => ⟨((1480995527/34359738368), (43901395/8589934592)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-240157019/17179869184), (-113904227/68719476736)), (21/8589934592), by norm_num⟩
  | 7 => ⟨((1068169099/274877906944), (31663913/68719476736)), (47/68719476736), by norm_num⟩
  | 8 => ⟨((-1039280545/1099511627776), (-123230259/1099511627776)), (185/1099511627776), by norm_num⟩
  | 9 => ⟨((1797641387/8796093022208), (213151121/8796093022208)), (161/4398046511104), by norm_num⟩
  | 10 => ⟨((-174902431/4398046511104), (-41477293/8796093022208)), (63/8796093022208), by norm_num⟩
  | 11 => ⟨((990092845/140737488355328), (58698971/70368744177664)), (45/35184372088832), by norm_num⟩
  | 12 => ⟨((-160552643/140737488355328), (-152297231/1125899906842624)), (235/1125899906842624), by norm_num⟩
  | 13 => ⟨((769036351/4503599627370496), (182373371/9007199254740992)), (283/9007199254740992), by norm_num⟩
  | 14 => ⟨((-1710257875/72057594037927936), (-202789825/72057594037927936)), (79/18014398509481984), by norm_num⟩
  | 15 => ⟨((443734421/144115188075855872), (105229541/288230376151711744)), (165/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1726934627/4611686018427387904), (-6249/140737488355328)), (323/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-3938538866007/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779368537841299/633825300114114700748351602688), (-4664104284531/633825300114114700748351602688)), (92659/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890415857375499/39614081257132168796771975168), (-5246307809347/39614081257132168796771975168)), (104271/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945116065247985/1237940039285380274899124224), (-5573243668561/2475880078570760549798248448)), (55411/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771897339148499/154742504910672534362390528), (-1393041331385/38685626227668133590597632)), (27715/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((24222106343923/151115727451828646838272), (-5222759233181/9671406556917033397649408)), (103973/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259366286875735/604462909807314587353088), (-4568768546727/604462909807314587353088)), (91017/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888728580002117/75557863725914323419136), (-1855525124677/18889465931478580854784)), (73989/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298240043978945/4722366482869645213696), (-2782347742863/2361183241434822606848)), (111051/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811204243211915/295147905179352825856), (-7648401386979/590295810358705651712)), (38201/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912335337940121/36893488147419103232), (-9555919224489/73786976294838206464)), (2987/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1823996391201831/9223372036854775808), (-10744107937759/9223372036854775808)), (215289/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595237317990963/1152921504606846976), (-10736231099513/1152921504606846976)), (107785/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195667275008877/144115188075855872), (-4692670150007/72057594037927936)), (188941/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493250178826033/36028797018963968), (-7030142747041/18014398509481984)), (71011/9007199254740992), by norm_num⟩
  | 3 => ⟨((372810999246513/2251799813685248), (-548260492501/281474976710656)), (178083/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115916031150925/2251799813685248), (-17497799508609/2251799813685248)), (357835/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110854588725773/1125899906842624), (-26130343823085/1125899906842624)), (540933/1125899906842624), by norm_num⟩
  | 0 => ⟨((1095534172924877/1125899906842624), (-3237199188919/70368744177664)), (549321/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095534172924877/1125899906842624), (-3237199188919/70368744177664)), (2095493318797874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((4154705685903/4398046511104), (-100796522020387/1125899906842624)), (1119553/562949953421312), by norm_num⟩
  | 2 => ⟨((124466539801893/140737488355328), (-190439042470347/1125899906842624)), (2315675/562949953421312), by norm_num⟩
  | 3 => ⟨((424201039201655/562949953421312), (-336843991412221/1125899906842624)), (4879275/562949953421312), by norm_num⟩
  | 4 => ⟨((1077044608323767/2251799813685248), (-253822867090565/562949953421312)), (41091693/2251799813685248), by norm_num⟩
  | 5 => ⟨((114760043770181/4503599627370496), (-1942471431484969/4503599627370496)), (152726957/4503599627370496), by norm_num⟩
  | 6 => ⟨((-26090417288357/140737488355328), (-197991051553307/9007199254740992)), (139530483/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-894041961/16777216)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-238848129/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((690958193097023/4503599627370496), (-579650354903035/9007199254740992)), (65161485/4503599627370496), by norm_num⟩
  | 1 => ⟨((-85640381/268435456), (574755205/4294967296)), (131/4294967296), by norm_num⟩
  | 2 => ⟨((1424673327/4294967296), (-597584925/4294967296)), (139/4294967296), by norm_num⟩
  | 3 => ⟨((-246877075/1073741824), (207107153/2147483648)), (49/2147483648), by norm_num⟩
  | 4 => ⟨((1026732891/8589934592), (-215333609/4294967296)), (13/1073741824), by norm_num⟩
  | 5 => ⟨((-427006205/8589934592), (179109461/8589934592)), (89/17179869184), by norm_num⟩
  | 6 => ⟨((295978147/17179869184), (-62074609/8589934592)), (63/34359738368), by norm_num⟩
  | 7 => ⟨((-1406786867/274877906944), (147520595/68719476736)), (19/34359738368), by norm_num⟩
  | 8 => ⟨((731332763/549755813888), (-613520907/1099511627776)), (161/1099511627776), by norm_num⟩
  | 9 => ⟨((-1351789981/4398046511104), (141753429/1099511627776)), (151/4398046511104), by norm_num⟩
  | 10 => ⟨((1124387297/17592186044416), (-235814375/8796093022208)), (1/137438953472), by norm_num⟩
  | 11 => ⟨((-850217329/70368744177664), (89156765/17592186044416)), (49/35184372088832), by norm_num⟩
  | 12 => ⟨((1178651489/562949953421312), (-247195041/281474976710656)), (69/281474976710656), by norm_num⟩
  | 13 => ⟨((-1508268843/4503599627370496), (79081175/562949953421312)), (45/1125899906842624), by norm_num⟩
  | 14 => ⟨((56006373/1125899906842624), (-375873555/18014398509481984)), (109/18014398509481984), by norm_num⟩
  | 15 => ⟨((-248452221/36028797018963968), (52107139/18014398509481984)), (123/144115188075855872), by norm_num⟩
  | 16 => ⟨((1033283739/1152921504606846976), (-216707499/576460752303423488)), (65/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-517350157417/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444800580755393/158456325028528675187087900672), (-612541052181/633825300114114700748351602688)), (92261/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118139347147859/2475880078570760549798248448), (-86125012607/4951760157141521099596496896)), (103797/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945017531215185/1237940039285380274899124224), (-731928678355/2475880078570760549798248448)), (110289/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771701259297181/154742504910672534362390528), (-731778054975/154742504910672534362390528)), (55147/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550032030597151/9671406556917033397649408), (-685881932381/9671406556917033397649408)), (51703/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157400925904791/75557863725914323419136), (-599986745263/604462909807314587353088)), (45243/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888472365916503/75557863725914323419136), (-487339333159/37778931862957161709568)), (147049/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649024800903223/2361183241434822606848), (-730746782517/4722366482869645213696)), (13787/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622149418446745/590295810358705651712), (-1004350916333/590295810358705651712)), (151671/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824351021766723/73786976294838206464), (-1254800119175/73786976294838206464)), (94805/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455910630562679/2305843009213693952), (-352693177435/2305843009213693952)), (213341/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594890616323427/1152921504606846976), (-352419188157/288230376151711744)), (106689/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195371960330105/144115188075855872), (-616117668955/72057594037927936)), (46687/36028797018963968), by norm_num⟩
  | 4 => ⟨((373205817651851/9007199254740992), (-1845892190587/36028797018963968)), (280205/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490738395213217/9007199254740992), (-2303065158349/9007199254740992)), (350403/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115452323491083/2251799813685248), (-2296627716643/2251799813685248)), (350625/2251799813685248), by norm_num⟩
  | 1 => ⟨((555131608378687/562949953421312), (-6857784516711/2251799813685248)), (263247/562949953421312), by norm_num⟩
  | 0 => ⟨((2189529836582069/2251799813685248), (-13587704582729/2251799813685248)), (2110457/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189529836582069/2251799813685248), (-13587704582729/2251799813685248)), (8050754555709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((133056240457987/140737488355328), (-26423916028183/2251799813685248)), (2064831/1125899906842624), by norm_num⟩
  | 2 => ⟨((251549688668697/281474976710656), (-49963474067561/2251799813685248)), (7905463/2251799813685248), by norm_num⟩
  | 3 => ⟨((1797338894114143/2251799813685248), (-22325779174717/562949953421312)), (14480789/2251799813685248), by norm_num⟩
  | 4 => ⟨((1431056186282173/2251799813685248), (-142559710710523/2251799813685248)), (24265093/2251799813685248), by norm_num⟩
  | 5 => ⟨((1800869264537583/4503599627370496), (-90599064218329/1125899906842624)), (67828297/4503599627370496), by norm_num⟩
  | 6 => ⟨((690958193097023/4503599627370496), (-579650354903035/9007199254740992)), (65161485/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-238848129/4194304)), (1/16777216), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile041Terms0

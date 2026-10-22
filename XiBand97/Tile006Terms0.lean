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
namespace Reinmann.XiBand97.Tile006Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10993/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10993/640))
  have he : value ((69/80), (10993/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1597980951/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((978026805479131/2251799813685248), (379905677832059/1125899906842624)), (31841159/2251799813685248), by norm_num⟩
  | 1 => ⟨((-80813947/268435456), (-125565791/536870912)), (23/2147483648), by norm_num⟩
  | 2 => ⟨((112031919/1073741824), (43517787/536870912)), (17/4294967296), by norm_num⟩
  | 3 => ⟨((-828315827/34359738368), (-321751801/17179869184)), (33/34359738368), by norm_num⟩
  | 4 => ⟨((143536195/34359738368), (892085415/274877906944)), (3/17179869184), by norm_num⟩
  | 5 => ⟨((-636746937/1099511627776), (-61834649/137438953472)), (7/274877906944), by norm_num⟩
  | 6 => ⟨((1176958251/17592186044416), (914357603/17592186044416)), (27/8796093022208), by norm_num⟩
  | 7 => ⟨((-932348907/140737488355328), (-362162511/70368744177664)), (45/140737488355328), by norm_num⟩
  | 8 => ⟨((80781877/140737488355328), (502063847/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 9 => ⟨((-796355275/18014398509481984), (-618674027/18014398509481984)), (43/18014398509481984), by norm_num⟩
  | 10 => ⟨((441593131/144115188075855872), (171532863/72057594037927936)), (49/288230376151711744), by norm_num⟩
  | 11 => ⟨((-890440825/4611686018427387904), (-691767391/4611686018427387904)), (13/1152921504606846976), by norm_num⟩
  | 12 => ⟨((822942063/73786976294838206464), (319664411/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-702055349/1180591620717411303424), (-545414117/1180591620717411303424)), (45/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((1112291853/37778931862957161709568), (432059723/18889465931478580854784)), (37/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-822380759/604462909807314587353088), (-638892755/604462909807314587353088)), (57/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1140061809/19342813113834066795298816), (55355839/1208925819614629174706176)), (81/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (215088781483/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890523934487157/316912650057057350374175801344), (1020667113937/633825300114114700748351602688)), (5769/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((29567274232981/618970019642690137449562112), (1148188237631/39614081257132168796771975168)), (12981/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892240513355545/2475880078570760549798248448), (1219875507847/2475880078570760549798248448)), (13793/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886953188977629/77371252455336267181195264), (1219791705317/154742504910672534362390528)), (6897/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776049488184167/4835703278458516698824704), (1143465688391/9671406556917033397649408)), (12933/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261015631888251/604462909807314587353088), (500221723725/302231454903657293676544)), (22635/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236426258679503/9444732965739290427392), (101597105165/4722366482869645213696)), (18393/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300252300752157/4722366482869645213696), (1219019219031/4722366482869645213696)), (27593/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812588594700877/295147905179352825856), (52372316503/18446744073709551616)), (18973/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828134325811319/73786976294838206464), (1047268375513/36893488147419103232)), (23721/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228487100229437/1152921504606846976), (2355864531675/9223372036854775808)), (6673/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399785618819815/288230376151711744), (2355252982811/1152921504606846976)), (6675/144115188075855872), by norm_num⟩
  | 5 => ⟨((1199089615361883/144115188075855872), (2060158494925/144115188075855872)), (23371/72057594037927936), by norm_num⟩
  | 4 => ⟨((749197157087923/18014398509481984), (386107791369/4503599627370496)), (70147/36028797018963968), by norm_num⟩
  | 3 => ⟨((93605793171591/562949953421312), (964667915177/2251799813685248)), (1371/140737488355328), by norm_num⟩
  | 2 => ⟨((70149523386501/140737488355328), (3855063715567/2251799813685248)), (43917/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120637745555935/1125899906842624), (2886790365937/562949953421312)), (131977/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115372175440803/1125899906842624), (11511132235735/1125899906842624)), (264859/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115372175440803/1125899906842624), (11511132235735/1125899906842624)), (1010356907371139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((138103149314417/140737488355328), (178179646087/8796093022208)), (265091/562949953421312), by norm_num⟩
  | 2 => ⟨((1083682966854699/1125899906842624), (11190045492341/281474976710656)), (1061997/1125899906842624), by norm_num⟩
  | 3 => ⟨((520634779182437/562949953421312), (21540923175641/281474976710656)), (2128793/1125899906842624), by norm_num⟩
  | 4 => ⟨((1912813216686327/2251799813685248), (318748157637165/2251799813685248)), (8526769/2251799813685248), by norm_num⟩
  | 5 => ⟨((197467265535423/281474976710656), (541527435091981/2251799813685248)), (4225067/562949953421312), by norm_num⟩
  | 6 => ⟨((978026805479131/2251799813685248), (379905677832059/1125899906842624)), (31841159/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1597980951/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1266369943/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1745615130722963/4503599627370496), (-18180356303643/2251799813685248)), (53916575/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1828912959/4294967296), (38095785/4294967296)), (59/4294967296), by norm_num⟩
  | 2 => ⟨((502316563/2147483648), (-20926249/4294967296)), (17/2147483648), by norm_num⟩
  | 3 => ⟨((-183950383/2147483648), (3831639/2147483648)), (13/4294967296), by norm_num⟩
  | 4 => ⟨((1616721211/68719476736), (-16837943/34359738368)), (15/17179869184), by norm_num⟩
  | 5 => ⟨((-177614979/34359738368), (14798697/137438953472)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((520346663/549755813888), (-10838687/549755813888)), (83/2199023255552), by norm_num⟩
  | 7 => ⟨((-163331211/1099511627776), (27217177/8796093022208)), (27/4398046511104), by norm_num⟩
  | 8 => ⟨((1435501405/70368744177664), (-29901125/70368744177664)), (31/35184372088832), by norm_num⟩
  | 9 => ⟨((-1401830653/562949953421312), (7299943/140737488355328)), (63/562949953421312), by norm_num⟩
  | 10 => ⟨((616027353/2251799813685248), (-25663383/4503599627370496)), (57/4503599627370496), by norm_num⟩
  | 11 => ⟨((-1968800641/72057594037927936), (10252403/18014398509481984)), (47/36028797018963968), by norm_num⟩
  | 12 => ⟨((1441965719/576460752303423488), (-469309/9007199254740992)), (71/576460752303423488), by norm_num⟩
  | 13 => ⟨((-974868467/4611686018427387904), (5076565/1152921504606846976)), (99/9223372036854775808), by norm_num⟩
  | 14 => ⟨((76500177/4611686018427387904), (-25495665/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-1434351523/1180591620717411303424), (14938587/590295810358705651712)), (77/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((787898105/9444732965739290427392), (-32823431/18889465931478580854784)), (87/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-13564570667/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890254077907039/316912650057057350374175801344), (-32165647713/633825300114114700748351602688)), (23051/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472924612365153/9903520314283042199192993792), (-36183285379/39614081257132168796771975168)), (51865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891595560016365/2475880078570760549798248448), (-2402563937/154742504910672534362390528)), (55107/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443315382011569/38685626227668133590597632), (-38436841179/154742504910672534362390528)), (55107/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551494539456945/9671406556917033397649408), (-36030096073/9671406556917033397649408)), (51663/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260486859450727/604462909807314587353088), (-985059133/18889465931478580854784)), (45205/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472637755043367/18889465931478580854784), (-51214748067/75557863725914323419136)), (73459/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324902048492787/1180591620717411303424), (-9600944149/1180591620717411303424)), (55095/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406072958818607/147573952589676412928), (-52793358469/590295810358705651712)), (75755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827028072069217/73786976294838206464), (-32986975805/36893488147419103232)), (94693/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456663217419745/2305843009213693952), (-37098151179/4611686018427387904)), (106531/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597899296940623/1152921504606846976), (-74165823153/1152921504606846976)), (26633/288230376151711744), by norm_num⟩
  | 5 => ⟨((149750335241599/18014398509481984), (-64860823057/144115188075855872)), (93217/144115188075855872), by norm_num⟩
  | 4 => ⟨((93547850512335/2251799813685248), (-97222732419/36028797018963968)), (139827/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495659770656725/9007199254740992), (-30352157925/2251799813685248)), (43697/2251799813685248), by norm_num⟩
  | 2 => ⟨((2240727785731449/4503599627370496), (-30307286437/562949953421312)), (349587/4503599627370496), by norm_num⟩
  | 1 => ⟨((2235212207394545/2251799813685248), (-362791334555/2251799813685248)), (131103/562949953421312), by norm_num⟩
  | 0 => ⟨((138669138933441/140737488355328), (-180501552397/562949953421312)), (1048957/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138669138933441/140737488355328), (-180501552397/562949953421312)), (4001453408248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((68315586276815/70368744177664), (-711395240587/1125899906842624)), (516939/562949953421312), by norm_num⟩
  | 2 => ⟨((530578444279115/562949953421312), (-690638770141/562949953421312)), (502183/281474976710656), by norm_num⟩
  | 3 => ⟨((62508444765127/70368744177664), (-5207397808537/2251799813685248)), (7582751/2251799813685248), by norm_num⟩
  | 4 => ⟨((888412429393951/1125899906842624), (-4625723282245/1125899906842624)), (3376641/562949953421312), by norm_num⟩
  | 5 => ⟨((175249869590783/281474976710656), (-14600054707911/2251799813685248)), (21426199/2251799813685248), by norm_num⟩
  | 6 => ⟨((1745615130722963/4503599627370496), (-18180356303643/2251799813685248)), (53916575/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1266369943/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1597980951/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((84204451420345/1125899906842624), (660019481688135/2251799813685248)), (49610353/2251799813685248), by norm_num⟩
  | 1 => ⟨((-222648919/2147483648), (-109074269/268435456)), (17/536870912), by norm_num⟩
  | 2 => ⟨((308656941/4294967296), (1209672353/4294967296)), (3/134217728), by norm_num⟩
  | 3 => ⟨((-285259585/8589934592), (-1117974641/8589934592)), (91/8589934592), by norm_num⟩
  | 4 => ⟨((197726877/17179869184), (1549841941/34359738368)), (1/268435456), by norm_num⟩
  | 5 => ⟨((-54821531/17179869184), (-859414857/68719476736)), (73/68719476736), by norm_num⟩
  | 6 => ⟨((405326823/549755813888), (198566995/68719476736)), (137/549755813888), by norm_num⟩
  | 7 => ⟨((-160543511/1099511627776), (-629193841/1099511627776)), (111/2199023255552), by norm_num⟩
  | 8 => ⟨((55640141/2199023255552), (436123937/4398046511104)), (39/4398046511104), by norm_num⟩
  | 9 => ⟨((-274252849/70368744177664), (-134354701/8796093022208)), (49/35184372088832), by norm_num⟩
  | 10 => ⟨((152078071/281474976710656), (298008263/140737488355328)), (111/562949953421312), by norm_num⟩
  | 11 => ⟨((-306654505/4503599627370496), (-300456127/1125899906842624)), (57/2251799813685248), by norm_num⟩
  | 12 => ⟨((283408941/36028797018963968), (277680423/9007199254740992)), (107/36028797018963968), by norm_num⟩
  | 13 => ⟨((-60444341/72057594037927936), (-947561365/288230376151711744)), (93/288230376151711744), by norm_num⟩
  | 14 => ⟨((191528341/2305843009213693952), (750627987/2305843009213693952)), (75/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-70803909/9223372036854775808), (-554982051/18446744073709551616)), (113/36893488147419103232), by norm_num⟩
  | 16 => ⟨((392620239/590295810358705651712), (96171061/36893488147419103232)), (159/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1720710251863/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780122799403511/633825300114114700748351602688), (2039325031659/633825300114114700748351602688)), (46201/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891264833787521/39614081257132168796771975168), (2293993685759/39614081257132168796771975168)), (51983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945567364846007/1237940039285380274899124224), (2437070575307/2475880078570760549798248448)), (55239/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886400284952917/77371252455336267181195264), (609183918837/38685626227668133590597632)), (55247/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551062255457599/9671406556917033397649408), (1142041951617/4835703278458516698824704)), (51803/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260108475278263/604462909807314587353088), (1998217666563/604462909807314587353088)), (45337/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944967945827113/37778931862957161709568), (811609192991/18889465931478580854784)), (9211/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1299146625270501/4722366482869645213696), (2434244102545/4722366482869645213696)), (55281/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623656817332523/590295810358705651712), (3346137665723/590295810358705651712)), (76035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913116879329481/36893488147419103232), (522656302955/9223372036854775808)), (95079/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912879262014275/4611686018427387904), (1175488110215/2305843009213693952)), (107013/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12476593934695/9007199254740992), (4699510325901/1152921504606846976)), (53537/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197218275812427/144115188075855872), (4109325176581/144115188075855872)), (93759/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495586919102629/36028797018963968), (6158497600189/36028797018963968)), (17597/4503599627370496), by norm_num⟩
  | 3 => ⟨((1494182778546365/9007199254740992), (7688519956815/9007199254740992)), (176211/9007199254740992), by norm_num⟩
  | 2 => ⟨((559440736417311/1125899906842624), (7674128385441/2251799813685248)), (88287/1125899906842624), by norm_num⟩
  | 1 => ⟨((278842241853847/281474976710656), (11475253896713/1125899906842624)), (265769/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104825194515337/1125899906842624), (178179646087/8796093022208)), (535179/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104825194515337/1125899906842624), (178179646087/8796093022208)), (2041545872214889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1083682966854701/1125899906842624), (11190045492341/281474976710656)), (536003/562949953421312), by norm_num⟩
  | 2 => ⟨((520634779182439/562949953421312), (21540923175641/281474976710656)), (268607/140737488355328), by norm_num⟩
  | 3 => ⟨((956406608343171/1125899906842624), (159374078818583/1125899906842624)), (8607131/2251799813685248), by norm_num⟩
  | 4 => ⟨((1579738124283409/2251799813685248), (270763717545993/1125899906842624)), (17059547/2251799813685248), by norm_num⟩
  | 5 => ⟨((978026805479163/2251799813685248), (759811355664137/2251799813685248)), (16070625/1125899906842624), by norm_num⟩
  | 6 => ⟨((84204451420345/1125899906842624), (660019481688135/2251799813685248)), (49610353/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1597980951/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1855198433/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-56766484491399/281474976710656), (-661843201407139/4503599627370496)), (50420101/2251799813685248), by norm_num⟩
  | 1 => ⟨((697037753/2147483648), (507924815/2147483648)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-560919493/2147483648), (-408736727/2147483648)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((1203686797/8589934592), (219278795/2147483648)), (141/8589934592), by norm_num⟩
  | 4 => ⟨((-968629583/17179869184), (-176457803/4294967296)), (115/17179869184), by norm_num⟩
  | 5 => ⟨((311789835/17179869184), (454396605/34359738368)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((-669075175/137438953472), (-487548749/137438953472)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((615334259/549755813888), (112097063/137438953472)), (153/1099511627776), by norm_num⟩
  | 8 => ⟨((-990342285/4398046511104), (-180413263/1099511627776)), (125/4398046511104), by norm_num⟩
  | 9 => ⟨((44274845/1099511627776), (258101285/8796093022208)), (91/17592186044416), by norm_num⟩
  | 10 => ⟨((-912097461/140737488355328), (-664636789/140737488355328)), (119/140737488355328), by norm_num⟩
  | 11 => ⟨((66725647/70368744177664), (777957561/1125899906842624)), (141/1125899906842624), by norm_num⟩
  | 12 => ⟨((-572750859/4503599627370496), (-417358131/4503599627370496)), (153/9007199254740992), by norm_num⟩
  | 13 => ⟨((1134531627/72057594037927936), (826722461/72057594037927936)), (77/36028797018963968), by norm_num⟩
  | 14 => ⟨((-521702347/288230376151711744), (-760319127/576460752303423488)), (9/36028797018963968), by norm_num⟩
  | 15 => ⟨((895624039/4611686018427387904), (326316381/2305843009213693952)), (125/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-360362821/18446744073709551616), (-525185955/36893488147419103232)), (51/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-817997673565/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779819916500247/633825300114114700748351602688), (-969154472797/158456325028528675187087900672)), (46291/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472730947705187/9903520314283042199192993792), (-1090159759179/9903520314283042199192993792)), (26045/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945385995238241/1237940039285380274899124224), (-2316260222797/1237940039285380274899124224)), (865/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1772437402201027/154742504910672534362390528), (-4631779515717/154742504910672534362390528)), (55375/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193840166335451/1208925819614629174706176), (-135672063893/302231454903657293676544)), (12983/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259809711296621/604462909807314587353088), (-59344226913/9444732965739290427392)), (45457/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472362386987297/18889465931478580854784), (-1542580860541/18889465931478580854784)), (73899/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298781122309497/4722366482869645213696), (-4626450912755/4722366482869645213696)), (13863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202894130102623/73786976294838206464), (-6359270984341/590295810358705651712)), (19073/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825602224825571/73786976294838206464), (-7945940097725/73786976294838206464)), (11929/9223372036854775808), by norm_num⟩
  | 7 => ⟨((114065347382029/576460752303423488), (-8934853077075/9223372036854775808)), (53727/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596287948963919/1152921504606846976), (-8929440920641/1152921504606846976)), (107571/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37393381839393/4503599627370496), (-3903585902791/72057594037927936)), (5891/9007199254740992), by norm_num⟩
  | 4 => ⟨((373658716204011/9007199254740992), (-11698578917907/36028797018963968)), (141647/36028797018963968), by norm_num⟩
  | 3 => ⟨((186622568434679/1125899906842624), (-14601909038875/9007199254740992)), (177519/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117661061489019/2251799813685248), (-7284966904587/1125899906842624)), (178211/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113493125389651/1125899906842624), (-10887475814809/562949953421312)), (269049/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100893962904437/1125899906842624), (-10807511411857/281474976710656)), (545047/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100893962904437/1125899906842624), (-10807511411857/281474976710656)), (2079189304832076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1074783533916663/1125899906842624), (-10567479395837/140737488355328)), (1107739/1125899906842624), by norm_num⟩
  | 2 => ⟨((254910017771421/281474976710656), (-161403375637537/1125899906842624)), (71289/35184372088832), by norm_num⟩
  | 3 => ⟨((112533851670141/140737488355328), (-292340994804845/1125899906842624)), (1196489/281474976710656), by norm_num⟩
  | 4 => ⟨((1287901838769337/2251799813685248), (-935024733805389/2251799813685248)), (2534767/281474976710656), by norm_num⟩
  | 5 => ⟨((174176205342569/1125899906842624), (-1069562282263421/2251799813685248)), (40036249/2251799813685248), by norm_num⟩
  | 6 => ⟨((-56766484491399/281474976710656), (-661843201407139/4503599627370496)), (50420101/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1855198433/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1032680209/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((770444003092703/4503599627370496), (71652487291911/562949953421312)), (49442015/4503599627370496), by norm_num⟩
  | 1 => ⟨((-20570313/67108864), (-122436545/536870912)), (11/536870912), by norm_num⟩
  | 2 => ⟨((1179425699/4294967296), (219376839/1073741824)), (81/4294967296), by norm_num⟩
  | 3 => ⟨((-352207861/2147483648), (-262047019/2147483648)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((315535885/4294967296), (117381307/2147483648)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((-56536441/2147483648), (-673021019/34359738368)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((1080530171/137438953472), (50245491/8589934592)), (83/137438953472), by norm_num⟩
  | 7 => ⟨((-1106314381/549755813888), (-205777907/137438953472)), (87/549755813888), by norm_num⟩
  | 8 => ⟨((495562317/1099511627776), (737409027/2199023255552)), (5/137438953472), by norm_num⟩
  | 9 => ⟨((-789269755/8796093022208), (-146806623/2199023255552)), (65/8796093022208), by norm_num⟩
  | 10 => ⟨((565672623/35184372088832), (420867451/35184372088832)), (95/70368744177664), by norm_num⟩
  | 11 => ⟨((-184281687/70368744177664), (-68553931/35184372088832)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((440251277/1125899906842624), (655104827/2251799813685248)), (39/1125899906842624), by norm_num⟩
  | 13 => ⟨((-970860793/18014398509481984), (-361166239/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 14 => ⟨((994028011/144115188075855872), (92446147/18014398509481984)), (23/36028797018963968), by norm_num⟩
  | 15 => ⟨((-237474547/288230376151711744), (-88342005/144115188075855872)), (45/576460752303423488), by norm_num⟩
  | 16 => ⟨((850994537/9223372036854775808), (19785953/288230376151711744)), (41/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (833225994303/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792381510545/316912650057057350374175801344), (493470452439/316912650057057350374175801344)), (46149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890659717392355/39614081257132168796771975168), (1110156700917/39614081257132168796771975168)), (51921/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890492009167569/2475880078570760549798248448), (294838874703/618970019642690137449562112)), (55169/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772158091909671/154742504910672534362390528), (1179146304263/154742504910672534362390528)), (27587/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550460189949669/9671406556917033397649408), (1105227440607/9671406556917033397649408)), (25865/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629790962745191/302231454903657293676544), (483425923327/302231454903657293676544)), (11317/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889080730946561/75557863725914323419136), (785358906005/37778931862957161709568)), (2299/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((5072287800493/18446744073709551616), (1177674093483/4722366482869645213696)), (55183/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811388099542997/295147905179352825856), (1618710169037/590295810358705651712)), (4743/36893488147419103232), by norm_num⟩
  | 8 => ⟨((114070875866913/4611686018427387904), (505625133835/18446744073709551616)), (94877/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824522723742191/9223372036854775808), (2274093866009/9223372036854775808)), (13345/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595769987715887/1152921504606846976), (1136285383109/576460752303423488)), (53395/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196140477375085/144115188075855872), (124174202027/9007199254740992)), (93475/144115188075855872), by norm_num⟩
  | 4 => ⟨((373493545667655/9007199254740992), (2976759718265/36028797018963968)), (140279/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492173779424195/9007199254740992), (464371245681/1125899906842624)), (87733/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233765668825523/4503599627370496), (7412030032505/4503599627370496)), (351285/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224793673278459/2251799813685248), (11073372168805/2251799813685248)), (131953/562949953421312), by norm_num⟩
  | 0 => ⟨((1098983791811923/1125899906842624), (10984331389297/1125899906842624)), (529589/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098983791811923/1125899906842624), (10984331389297/1125899906842624)), (2020221714500045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((268150994548853/281474976710656), (42886946121457/2251799813685248)), (1044191/1125899906842624), by norm_num⟩
  | 2 => ⟨((1021422476824545/1125899906842624), (81713674089427/2251799813685248)), (2029301/1125899906842624), by norm_num⟩
  | 3 => ⟨((925157368517917/1125899906842624), (37065543247497/562949953421312)), (3829265/1125899906842624), by norm_num⟩
  | 4 => ⟨((755325347634955/1125899906842624), (121827740619343/1125899906842624)), (13594603/2251799813685248), by norm_num⟩
  | 5 => ⟨((987075989647671/2251799813685248), (326919222483775/2251799813685248)), (21182253/2251799813685248), by norm_num⟩
  | 6 => ⟨((770444003092703/4503599627370496), (71652487291911/562949953421312)), (49442015/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1032680209/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-560762461/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-356068689496313/4503599627370496), (-380809044583861/2251799813685248)), (147931745/9007199254740992), by norm_num⟩
  | 1 => ⟨((660779645/4294967296), (353345959/1073741824)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((-642908909/4294967296), (-21486859/67108864)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((104253581/1073741824), (891978603/4294967296)), (91/4294967296), by norm_num⟩
  | 4 => ⟨((-405736203/8589934592), (-216963777/2147483648)), (45/4294967296), by norm_num⟩
  | 5 => ⟨((157905239/8589934592), (675507225/17179869184)), (71/17179869184), by norm_num⟩
  | 6 => ⟨((-409692543/68719476736), (-876317577/68719476736)), (47/34359738368), by norm_num⟩
  | 7 => ⟨((455557073/274877906944), (974420153/274877906944)), (53/137438953472), by norm_num⟩
  | 8 => ⟨((-221618283/549755813888), (-948067033/1099511627776)), (105/1099511627776), by norm_num⟩
  | 9 => ⟨((383332681/4398046511104), (819934783/4398046511104)), (23/1099511627776), by norm_num⟩
  | 10 => ⟨((-149186191/8796093022208), (-1276415533/35184372088832)), (145/35184372088832), by norm_num⟩
  | 11 => ⟨((422258797/140737488355328), (451598171/70368744177664)), (13/17592186044416), by norm_num⟩
  | 12 => ⟨((-547785119/1125899906842624), (-1171692619/1125899906842624)), (17/140737488355328), by norm_num⟩
  | 13 => ⟨((163990865/2251799813685248), (701541095/4503599627370496)), (165/9007199254740992), by norm_num⟩
  | 14 => ⟨((-91174711/9007199254740992), (-390038839/18014398509481984)), (93/36028797018963968), by norm_num⟩
  | 15 => ⟨((378491297/288230376151711744), (404789619/144115188075855872)), (49/144115188075855872), by norm_num⟩
  | 16 => ⟨((-92063757/576460752303423488), (-196921057/576460752303423488)), (97/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-2615801491731/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779375037457311/633825300114114700748351602688), (-774422403849/158456325028528675187087900672)), (46253/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890423543710683/39614081257132168796771975168), (-3484375922567/39614081257132168796771975168)), (13011/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472560193912181/618970019642690137449562112), (-3701514415013/2475880078570760549798248448)), (13827/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771906522254627/154742504910672534362390528), (-3700800104287/154742504910672534362390528)), (55321/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387555996613065/2417851639229258349412352), (-3468741245447/9671406556917033397649408)), (51877/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314843722677019/151115727451828646838272), (-758597463255/151115727451828646838272)), (22703/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888743631046673/75557863725914323419136), (-2464730562713/37778931862957161709568)), (36905/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649126133822509/2361183241434822606848), (-461981437787/590295810358705651712)), (13845/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811213406317833/295147905179352825856), (-5079774221203/590295810358705651712)), (76183/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824695859331717/73786976294838206464), (-6346686191767/73786976294838206464)), (95283/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824027847885029/9223372036854775808), (-7135854848613/9223372036854775808)), (26817/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199409084455941/144115188075855872), (-3565323960545/576460752303423488)), (107361/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597851296892067/72057594037927936), (-779182730801/18014398509481984)), (47023/72057594037927936), by norm_num⟩
  | 4 => ⟨((11666499212687/281474976710656), (-9338489377913/36028797018963968)), (141279/36028797018963968), by norm_num⟩
  | 3 => ⟨((745668201363039/4503599627370496), (-5826323025009/4503599627370496)), (176967/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116031232464319/2251799813685248), (-5810989051219/1125899906842624)), (11095/140737488355328), by norm_num⟩
  | 1 => ⟨((555542037162165/562949953421312), (-8678202201925/562949953421312)), (133833/562949953421312), by norm_num⟩
  | 0 => ⟨((548109024262481/562949953421312), (-4300900220147/140737488355328)), (270445/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548109024262481/562949953421312), (-4300900220147/140737488355328)), (1031665804149436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1066267211750153/1125899906842624), (-16750066031897/281474976710656)), (1086321/1125899906842624), by norm_num⟩
  | 2 => ⟨((502902933279383/562949953421312), (-126903260909201/1125899906842624)), (546715/281474976710656), by norm_num⟩
  | 3 => ⟨((442109017650801/562949953421312), (-453468531375421/2251799813685248)), (1100043/281474976710656), by norm_num⟩
  | 4 => ⟨((1297509844838771/2251799813685248), (-178064253956779/562949953421312)), (4341755/562949953421312), by norm_num⟩
  | 5 => ⟨((522347383506353/2251799813685248), (-410409701819233/1125899906842624)), (3875085/281474976710656), by norm_num⟩
  | 6 => ⟨((-356068689496313/4503599627370496), (-380809044583861/2251799813685248)), (147931745/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-560762461/16777216)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1198485713/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-149561199713557/2251799813685248), (85873057497465/562949953421312)), (263126447/9007199254740992), by norm_num⟩
  | 1 => ⟨((593192619/4294967296), (-681182873/2147483648)), (33/536870912), by norm_num⟩
  | 2 => ⟨((-616754687/4294967296), (354119991/1073741824)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((106875443/1073741824), (-981829093/4294967296)), (195/4294967296), by norm_num⟩
  | 4 => ⟨((-55560309/1073741824), (1020828101/8589934592)), (205/8589934592), by norm_num⟩
  | 5 => ⟨((369710127/17179869184), (-53068809/1073741824)), (43/4294967296), by norm_num⟩
  | 6 => ⟨((-64065883/8589934592), (1177103851/68719476736)), (241/68719476736), by norm_num⟩
  | 7 => ⟨((152252867/68719476736), (-699348185/137438953472)), (145/137438953472), by norm_num⟩
  | 8 => ⟨((-633201873/1099511627776), (363563417/274877906944)), (19/68719476736), by norm_num⟩
  | 9 => ⟨((585202791/4398046511104), (-1344015773/4398046511104)), (71/1099511627776), by norm_num⟩
  | 10 => ⟨((-243378999/8796093022208), (279480223/4398046511104)), (239/17592186044416), by norm_num⟩
  | 11 => ⟨((368067201/70368744177664), (-105665961/8796093022208)), (183/70368744177664), by norm_num⟩
  | 12 => ⟨((-510249485/562949953421312), (1171873007/562949953421312)), (1/2199023255552), by norm_num⟩
  | 13 => ⟨((326471993/2251799813685248), (-374898679/1125899906842624)), (83/1125899906842624), by norm_num⟩
  | 14 => ⟨((-96982775/4503599627370496), (445474221/9007199254740992)), (25/2251799813685248), by norm_num⟩
  | 15 => ⟨((430229357/144115188075855872), (-988093441/144115188075855872)), (7/4503599627370496), by norm_num⟩
  | 16 => ⟨((-447318399/1152921504606846976), (513670637/576460752303423488)), (235/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (645266346875/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779197529281109/633825300114114700748351602688), (1527986882329/316912650057057350374175801344)), (92501/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890223886987405/39614081257132168796771975168), (3437419488313/39614081257132168796771975168)), (104083/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945014344067227/1237940039285380274899124224), (912897234903/618970019642690137449562112)), (55305/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771694488468625/154742504910672534362390528), (3650836113017/154742504910672534362390528)), (27659/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550025261861425/9671406556917033397649408), (427732388601/1208925819614629174706176)), (25937/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259201063771573/604462909807314587353088), (2993327120449/604462909807314587353088)), (45403/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472115317323553/18889465931478580854784), (4862657634419/75557863725914323419136)), (147609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298040589966045/4722366482869645213696), (1822840984913/2361183241434822606848)), (110751/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622135907972189/590295810358705651712), (5010682505033/590295810358705651712)), (76177/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912166228349135/36893488147419103232), (24453745525/288230376151711744)), (190549/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823619333656165/9223372036854775808), (7038288251865/9223372036854775808)), (214515/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594864553532083/1152921504606846976), (7032802685417/1152921504606846976)), (214699/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597672963993061/72057594037927936), (6147534536625/144115188075855872)), (94035/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492777782444531/36028797018963968), (2302243701155/9007199254740992)), (282519/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490670299678535/9007199254740992), (2872416417971/2251799813685248)), (353875/9007199254740992), by norm_num⟩
  | 2 => ⟨((34855232591737/70368744177664), (11457375275151/2251799813685248)), (44371/281474976710656), by norm_num⟩
  | 1 => ⟨((1110094170720343/1125899906842624), (2138184125367/140737488355328)), (133797/281474976710656), by norm_num⟩
  | 0 => ⟨((34195667030003/35184372088832), (2118087724529/70368744177664)), (1081355/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((34195667030003/35184372088832), (2118087724529/70368744177664)), (4125041965964889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1062491782908759/1125899906842624), (65874176078369/1125899906842624)), (1083517/562949953421312), by norm_num⟩
  | 2 => ⟨((1997600985381051/2251799813685248), (124328584386205/1125899906842624)), (8687123/2251799813685248), by norm_num⟩
  | 3 => ⟨((1744639681261899/2251799813685248), (441174035403183/2251799813685248)), (17331489/2251799813685248), by norm_num⟩
  | 4 => ⟨((1265269261771925/2251799813685248), (683621806724619/2251799813685248)), (33647225/2251799813685248), by norm_num⟩
  | 5 => ⟨((31462819298651/140737488355328), (12003809872841/35184372088832)), (58242103/2251799813685248), by norm_num⟩
  | 6 => ⟨((-149561199713557/2251799813685248), (85873057497465/562949953421312)), (263126447/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1198485713/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile006Terms0

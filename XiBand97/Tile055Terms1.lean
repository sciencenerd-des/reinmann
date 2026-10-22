/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile055Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨55,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77803/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77803/2560))
  have he : value ((69/80), (77803/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-17925476323/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-117394796299149/1125899906842624), (487535960685563/4503599627370496)), (30689823/9007199254740992), by norm_num⟩
  | 1 => ⟨((15743574931/68719476736), (-8172805749/34359738368)), (517/68719476736), by norm_num⟩
  | 2 => ⟨((-8648042443/34359738368), (8978744829/34359738368)), (143/17179869184), by norm_num⟩
  | 3 => ⟨((3166948567/17179869184), (-13152212541/68719476736)), (421/68719476736), by norm_num⟩
  | 4 => ⟨((-13916994453/137438953472), (14449182321/137438953472)), (465/137438953472), by norm_num⟩
  | 5 => ⟨((6115752451/137438953472), (-12699239407/274877906944)), (411/274877906944), by norm_num⟩
  | 6 => ⟨((-2239613599/137438953472), (9301026979/549755813888)), (303/549755813888), by norm_num⟩
  | 7 => ⟨((5623924621/1099511627776), (-11677968613/2199023255552)), (191/1099511627776), by norm_num⟩
  | 8 => ⟨((-6178512699/4398046511104), (12829559825/8796093022208)), (211/4398046511104), by norm_num⟩
  | 9 => ⟨((12067182181/35184372088832), (-6264316481/17592186044416)), (415/35184372088832), by norm_num⟩
  | 10 => ⟨((-10605723707/140737488355328), (5505644053/70368744177664)), (367/140737488355328), by norm_num⟩
  | 11 => ⟨((2118468799/140737488355328), (-4398958701/281474976710656)), (295/562949953421312), by norm_num⟩
  | 12 => ⟨((-6206335615/2251799813685248), (12887333563/4503599627370496)), (435/4503599627370496), by norm_num⟩
  | 13 => ⟨((2097955869/4503599627370496), (-17425456025/36028797018963968)), (591/36028797018963968), by norm_num⟩
  | 14 => ⟨((-1317051485/18014398509481984), (10939325785/144115188075855872)), (373/144115188075855872), by norm_num⟩
  | 15 => ⟨((385847719/36028797018963968), (-12819282919/1152921504606846976)), (55/144115188075855872), by norm_num⟩
  | 16 => ⟨((-13564705461/9223372036854775808), (14083421747/9223372036854775808)), (243/4611686018427387904), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (3044770503229/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779038908882163/633825300114114700748351602688), (3604395122101/633825300114114700748351602688)), (5785/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890045357652923/39614081257132168796771975168), (4054255567429/39614081257132168796771975168)), (13019/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944919446146477/1237940039285380274899124224), (4306812074011/2475880078570760549798248448)), (3459/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771504570765335/154742504910672534362390528), (4305873381795/154742504910672534362390528)), (865/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((193730885579789/1208925819614629174706176), (2017879539595/4835703278458516698824704)), (12979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629522514719813/302231454903657293676544), (3530292140101/604462909807314587353088)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472051867845599/18889465931478580854784), (2867427797779/37778931862957161709568)), (4617/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297850029918289/4722366482869645213696), (537438318841/590295810358705651712)), (6929/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810936772244855/295147905179352825856), (369322815103/36893488147419103232)), (2383/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824003988017033/73786976294838206464), (3691236367885/36893488147419103232)), (11923/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823249100482897/9223372036854775808), (8299806264997/9223372036854775808)), (839/288230376151711744), by norm_num⟩
  | 6 => ⟨((1594493439915035/1152921504606846976), (8292964575049/1152921504606846976)), (6719/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195020215736509/144115188075855872), (3624325452605/72057594037927936)), (23547/144115188075855872), by norm_num⟩
  | 4 => ⟨((746143622527025/18014398509481984), (10857599680299/36028797018963968)), (35381/36028797018963968), by norm_num⟩
  | 3 => ⟨((745026848555063/4503599627370496), (3386277964843/2251799813685248)), (44333/9007199254740992), by norm_num⟩
  | 2 => ⟨((557372861980923/1125899906842624), (13504823207513/2251799813685248)), (22247/1125899906842624), by norm_num⟩
  | 1 => ⟨((277287226359313/281474976710656), (20156663855307/1125899906842624)), (67145/1125899906842624), by norm_num⟩
  | 0 => ⟨((136540086281477/140737488355328), (4988993804009/140737488355328)), (67955/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((136540086281477/140737488355328), (4988993804009/140737488355328)), (259227754833030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1058328115424089/1125899906842624), (38721603030873/562949953421312)), (136675/562949953421312), by norm_num⟩
  | 2 => ⟨((247371223445643/281474976710656), (72795389559601/562949953421312)), (275747/562949953421312), by norm_num⟩
  | 3 => ⟨((850771613211673/1125899906842624), (255901747103745/1125899906842624)), (2223955/2251799813685248), by norm_num⟩
  | 4 => ⟨((1169423018289783/2251799813685248), (773475300544883/2251799813685248)), (1092989/562949953421312), by norm_num⟩
  | 5 => ⟨((85407920197621/562949953421312), (401687492395461/1125899906842624)), (7544425/2251799813685248), by norm_num⟩
  | 6 => ⟨((-117394796299149/1125899906842624), (487535960685563/4503599627370496)), (30689823/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-17925476323/268435456)), (1/134217728), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-18785032259/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((802170614584849/9007199254740992), (-940595556211073/9007199254740992)), (9186439/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3522998999/17179869184), (8261876321/34359738368)), (163/34359738368), by norm_num⟩
  | 2 => ⟨((4056002489/17179869184), (-2377959157/8589934592)), (95/17179869184), by norm_num⟩
  | 3 => ⟨((-778274239/4294967296), (7300604409/34359738368)), (147/34359738368), by norm_num⟩
  | 4 => ⟨((1792042661/17179869184), (-8405131441/68719476736)), (341/137438953472), by norm_num⟩
  | 5 => ⟨((-13204258295/274877906944), (483838259/8589934592)), (79/68719476736), by norm_num⟩
  | 6 => ⟨((10134642771/549755813888), (-11883506801/549755813888)), (245/549755813888), by norm_num⟩
  | 7 => ⟨((-13334787067/2199023255552), (15635877493/2199023255552)), (325/2199023255552), by norm_num⟩
  | 8 => ⟨((15352240959/8796093022208), (-18001469215/8796093022208)), (377/8796093022208), by norm_num⟩
  | 9 => ⟨((-15711040523/35184372088832), (2302773037/4398046511104)), (389/35184372088832), by norm_num⟩
  | 10 => ⟨((14470403081/140737488355328), (-2120932347/17592186044416)), (361/140737488355328), by norm_num⟩
  | 11 => ⟨((-1514515201/70368744177664), (14206915507/562949953421312)), (305/562949953421312), by norm_num⟩
  | 12 => ⟨((1162433375/281474976710656), (-10904210621/2251799813685248)), (59/562949953421312), by norm_num⟩
  | 13 => ⟨((-13177116361/18014398509481984), (7725499331/9007199254740992)), (337/18014398509481984), by norm_num⟩
  | 14 => ⟨((4334490243/36028797018963968), (-10164925483/72057594037927936)), (223/72057594037927936), by norm_num⟩
  | 15 => ⟨((-2661475365/144115188075855872), (12482989807/576460752303423488)), (69/144115188075855872), by norm_num⟩
  | 16 => ⟨((12256547001/4611686018427387904), (-14371573123/4611686018427387904)), (5/72057594037927936), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-1126316257229/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778904788913115/633825300114114700748351602688), (-83320732817/39614081257132168796771975168)), (5771/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944947420670959/19807040628566084398385987584), (-1499512045323/39614081257132168796771975168)), (6493/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944839721526875/1237940039285380274899124224), (-12444599693/19342813113834066795298816)), (13799/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885672827404143/77371252455336267181195264), (-796272871431/77371252455336267181195264)), (1725/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549698667224507/9671406556917033397649408), (-186578254659/1208925819614629174706176)), (12939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314728932535663/151115727451828646838272), (-1305662309481/604462909807314587353088)), (2831/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887998420406693/75557863725914323419136), (-2120978753191/75557863725914323419136)), (18403/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324423542191297/1180591620717411303424), (-397525534987/1180591620717411303424)), (13805/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810830370245641/295147905179352825856), (-273170506999/73786976294838206464)), (18985/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455935059543379/18446744073709551616), (-1365083175099/36893488147419103232)), (23737/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822955478725493/9223372036854775808), (-3069322800711/9223372036854775808)), (3339/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594203683151807/1152921504606846976), (-766670491217/288230376151711744)), (13361/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194771018408551/144115188075855872), (-2680378654795/144115188075855872)), (23393/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491922108069007/36028797018963968), (-2007319517947/18014398509481984)), (4389/4503599627370496), by norm_num⟩
  | 3 => ⟨((744806191345973/4503599627370496), (-5007939280483/9007199254740992)), (43929/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114326977027757/2251799813685248), (-9984864488083/4503599627370496)), (43989/2251799813685248), by norm_num⟩
  | 1 => ⟨((554288439950873/562949953421312), (-14899986763167/2251799813685248)), (66133/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182798162824721/2251799813685248), (-1843255092137/140737488355328)), (265737/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182798162824721/2251799813685248), (-1843255092137/140737488355328)), (1013706215865325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2115524660678013/2251799813685248), (-57176717813461/2251799813685248)), (261075/1125899906842624), by norm_num⟩
  | 2 => ⟨((1986044845415381/2251799813685248), (-107432957242363/2251799813685248)), (503809/1125899906842624), by norm_num⟩
  | 3 => ⟨((109158023944821/140737488355328), (-11844229539311/140737488355328)), (468387/562949953421312), by norm_num⟩
  | 4 => ⟨((1338683934836607/2251799813685248), (-293969763256443/2251799813685248)), (805413/562949953421312), by norm_num⟩
  | 5 => ⟨((1514927255357687/4503599627370496), (-699054324469587/4503599627370496)), (9343357/4503599627370496), by norm_num⟩
  | 6 => ⟨((802170614584849/9007199254740992), (-940595556211073/9007199254740992)), (9186439/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-18785032259/268435456)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-9781297593/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-115863454550315/1125899906842624), (661329021773493/9007199254740992)), (3225633/1125899906842624), by norm_num⟩
  | 1 => ⟨((16957301633/68719476736), (-1512334571/8589934592)), (237/34359738368), by norm_num⟩
  | 2 => ⟨((-2541364589/8589934592), (7252839837/34359738368)), (143/17179869184), by norm_num⟩
  | 3 => ⟨((4062617423/17179869184), (-5797183453/34359738368)), (115/17179869184), by norm_num⟩
  | 4 => ⟨((-4870865557/34359738368), (6950519399/68719476736)), (277/68719476736), by norm_num⟩
  | 5 => ⟨((9343860395/137438953472), (-1666661761/34359738368)), (267/137438953472), by norm_num⟩
  | 6 => ⟨((-14937065781/549755813888), (10657280955/549755813888)), (429/549755813888), by norm_num⟩
  | 7 => ⟨((10233576979/1099511627776), (-7301441035/1099511627776)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((-12269522931/4398046511104), (8754045471/4398046511104)), (357/4398046511104), by norm_num⟩
  | 9 => ⟨((6538006897/8796093022208), (-2332364917/4398046511104)), (191/8796093022208), by norm_num⟩
  | 10 => ⟨((-6270982333/35184372088832), (4474213447/35184372088832)), (369/70368744177664), by norm_num⟩
  | 11 => ⟨((5468057779/140737488355328), (-487667967/17592186044416)), (323/281474976710656), by norm_num⟩
  | 12 => ⟨((-8741219933/1125899906842624), (12473351603/2251799813685248)), (519/2251799813685248), by norm_num⟩
  | 13 => ⟨((12898787665/9007199254740992), (-1150376571/1125899906842624)), (385/9007199254740992), by norm_num⟩
  | 14 => ⟨((-17674252553/72057594037927936), (788137869/4503599627370496)), (265/36028797018963968), by norm_num⟩
  | 15 => ⟨((11301601773/288230376151711744), (-8063454167/288230376151711744)), (341/288230376151711744), by norm_num⟩
  | 16 => ⟨((-13550028733/2305843009213693952), (9667659315/2305843009213693952)), (411/2305843009213693952), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1642513589141/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778770914686445/633825300114114700748351602688), (3887700159243/633825300114114700748351602688)), (5787/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472435963840089/9903520314283042199192993792), (4372853604923/39614081257132168796771975168)), (407/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((472379631800849/618970019642690137449562112), (2322587344145/1237940039285380274899124224)), (13841/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771184184504403/154742504910672534362390528), (4644069746563/154742504910672534362390528)), (3461/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549546700096495/9671406556917033397649408), (1088160394127/2417851639229258349412352)), (1623/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629391085312389/302231454903657293676544), (3807387781625/604462909807314587353088)), (11365/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887780284092273/75557863725914323419136), (386550318887/4722366482869645213696)), (4619/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297529603121987/4722366482869645213696), (4636679242229/4722366482869645213696)), (1733/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810716449467161/295147905179352825856), (6372307358501/590295810358705651712)), (9537/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823453093572933/73786976294838206464), (7960695787319/73786976294838206464)), (23859/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911314612419681/4611686018427387904), (8949338616341/9223372036854775808)), (26865/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593873416404743/1152921504606846976), (4470643534661/576460752303423488)), (26895/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194477530703265/144115188075855872), (7814573195779/144115188075855872)), (11783/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491472893292159/36028797018963968), (2925941582161/9007199254740992)), (35415/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489035200611531/9007199254740992), (7299036270979/4503599627370496)), (1387/281474976710656), by norm_num⟩
  | 2 => ⟨((1113726413353663/2251799813685248), (14550675970143/2251799813685248)), (22279/1125899906842624), by norm_num⟩
  | 1 => ⟨((553808988878047/562949953421312), (21707720620419/1125899906842624)), (67273/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089251426514949/1125899906842624), (42943459723263/1125899906842624)), (136297/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089251426514949/1125899906842624), (42943459723263/1125899906842624)), (519931797507857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052157942488783/1125899906842624), (41545633389585/562949953421312)), (274119/1125899906842624), by norm_num⟩
  | 2 => ⟨((488556829359893/562949953421312), (77649119394925/562949953421312)), (69099/140737488355328), by norm_num⟩
  | 3 => ⟨((1653137287656991/2251799813685248), (269551546055683/1125899906842624)), (1111979/1125899906842624), by norm_num⟩
  | 4 => ⟨((1084568323114377/2251799813685248), (791554753707829/2251799813685248)), (4330271/2251799813685248), by norm_num⟩
  | 5 => ⟨((244128947895237/2251799813685248), (190624230152395/562949953421312)), (14431339/4503599627370496), by norm_num⟩
  | 6 => ⟨((-115863454550315/1125899906842624), (661329021773493/9007199254740992)), (3225633/1125899906842624), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-9781297593/134217728)), (1/134217728), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-20272454521/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((262099560910423/2251799813685248), (-32283261237053/2251799813685248)), (4578323/4503599627370496), by norm_num⟩
  | 1 => ⟨((-9937941617/34359738368), (1224073647/34359738368)), (175/68719476736), by norm_num⟩
  | 2 => ⟨((24694857209/68719476736), (-3041708745/68719476736)), (55/17179869184), by norm_num⟩
  | 3 => ⟨((-20454804965/68719476736), (157465881/4294967296)), (23/8589934592), by norm_num⟩
  | 4 => ⟨((25414140439/137438953472), (-3130304119/137438953472)), (231/137438953472), by norm_num⟩
  | 5 => ⟨((-12630353315/137438953472), (97231419/8589934592)), (29/34359738368), by norm_num⟩
  | 6 => ⟨((20923499295/549755813888), (-644295999/137438953472)), (97/274877906944), by norm_num⟩
  | 7 => ⟨((-29710252877/2199023255552), (457432975/274877906944)), (139/1099511627776), by norm_num⟩
  | 8 => ⟨((18456801235/4398046511104), (-2273356483/4398046511104)), (175/4398046511104), by norm_num⟩
  | 9 => ⟨((-2547968229/2199023255552), (2510701619/17592186044416)), (49/4398046511104), by norm_num⟩
  | 10 => ⟨((10130341113/35184372088832), (-2495543659/70368744177664)), (197/70368744177664), by norm_num⟩
  | 11 => ⟨((-4576900363/70368744177664), (2254979285/281474976710656)), (45/70368744177664), by norm_num⟩
  | 12 => ⟨((30328453727/2251799813685248), (-466951085/281474976710656)), (301/2251799813685248), by norm_num⟩
  | 13 => ⟨((-23188731183/9007199254740992), (2856196569/9007199254740992)), (29/1125899906842624), by norm_num⟩
  | 14 => ⟨((8231690331/18014398509481984), (-2027823385/36028797018963968)), (83/18014398509481984), by norm_num⟩
  | 15 => ⟨((-2727330939/36028797018963968), (2687440967/288230376151711744)), (111/144115188075855872), by norm_num⟩
  | 16 => ⟨((13554325573/1152921504606846976), (-3339019965/2305843009213693952)), (139/1152921504606846976), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (-79820438231/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889331650433205/316912650057057350374175801344), (-188905284095/633825300114114700748351602688)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944811634624127/19807040628566084398385987584), (-53119693567/9903520314283042199192993792)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889391027214815/2475880078570760549798248448), (-112854678305/1237940039285380274899124224)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771057384581539/154742504910672534362390528), (-56413467447/38685626227668133590597632)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((24209821383237/151115727451828646838272), (-211491567471/9671406556917033397649408)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258679548340877/604462909807314587353088), (-184996207793/604462909807314587353088)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887614914601991/75557863725914323419136), (-300508420511/75557863725914323419136)), (9185/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297406792658237/4722366482869645213696), (-225284746467/4722366482869645213696)), (6889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810633004772213/295147905179352825856), (-309609688281/590295810358705651712)), (18945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823247440721099/73786976294838206464), (-386777004249/73786976294838206464)), (11841/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822401927985323/9223372036854775808), (-434801104189/9223372036854775808)), (26643/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796825594509643/576460752303423488), (-217198844917/576460752303423488)), (26645/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194288772824737/144115188075855872), (-189822321221/72057594037927936)), (5829/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491201108510989/36028797018963968), (-35535097017/2251799813685248)), (34977/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488715268015029/9007199254740992), (-709120303301/9007199254740992)), (43727/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113436043234503/2251799813685248), (-1413507006073/4503599627370496)), (87471/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214511714371949/2251799813685248), (-2108466000531/2251799813685248)), (131253/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177636208409997/2251799813685248), (-4169990170465/2251799813685248)), (32837/281474976710656), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177636208409997/2251799813685248), (-4169990170465/2251799813685248)), (125263215185069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2105907478338163/2251799813685248), (-8065300946141/2251799813685248)), (254531/1125899906842624), by norm_num⟩
  | 2 => ⟨((1969438504830223/2251799813685248), (-15085512907765/2251799813685248)), (29869/70368744177664), by norm_num⟩
  | 3 => ⟨((1722382437389409/2251799813685248), (-26387771954775/2251799813685248)), (1684719/2251799813685248), by norm_num⟩
  | 4 => ⟨((658563192006133/1125899906842624), (-20183781302637/1125899906842624)), (2616741/2251799813685248), by norm_num⟩
  | 5 => ⟨((48105751919451/140737488355328), (-94447439674769/4503599627370496)), (6309993/4503599627370496), by norm_num⟩
  | 6 => ⟨((262099560910423/2251799813685248), (-32283261237053/2251799813685248)), (4578323/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-20272454521/268435456)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-1307841363/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-410579653994079/4503599627370496), (-545536515773215/9007199254740992)), (11174309/4503599627370496), by norm_num⟩
  | 1 => ⟨((16069275203/68719476736), (2668902465/17179869184)), (439/68719476736), by norm_num⟩
  | 2 => ⟨((-20608438553/68719476736), (-13691199325/68719476736)), (565/68719476736), by norm_num⟩
  | 3 => ⟨((17619867075/68719476736), (731609019/4294967296)), (243/34359738368), by norm_num⟩
  | 4 => ⟨((-11298516683/68719476736), (-7506160333/68719476736)), (313/68719476736), by norm_num⟩
  | 5 => ⟨((5796024621/68719476736), (7701168449/137438953472)), (323/137438953472), by norm_num⟩
  | 6 => ⟨((-4955503209/137438953472), (-13168738043/549755813888)), (555/549755813888), by norm_num⟩
  | 7 => ⟨((7263208441/549755813888), (9650613195/1099511627776)), (409/1099511627776), by norm_num⟩
  | 8 => ⟨((-582180057/137438953472), (-12376667057/4398046511104)), (527/4398046511104), by norm_num⟩
  | 9 => ⟨((5309377291/4398046511104), (7054560937/8796093022208)), (151/4398046511104), by norm_num⟩
  | 10 => ⟨((-10894627097/35184372088832), (-7237836617/35184372088832)), (39/4398046511104), by norm_num⟩
  | 11 => ⟨((20323030379/281474976710656), (421924645/8796093022208)), (585/281474976710656), by norm_num⟩
  | 12 => ⟨((-542995247/35184372088832), (-11543630369/1125899906842624)), (251/562949953421312), by norm_num⟩
  | 13 => ⟨((13713283051/4503599627370496), (9110408399/4503599627370496)), (199/2251799813685248), by norm_num⟩
  | 14 => ⟨((-5024839507/9007199254740992), (-417281003/1125899906842624)), (293/18014398509481984), by norm_num⟩
  | 15 => ⟨((859230591/9007199254740992), (4566633133/72057594037927936)), (403/144115188075855872), by norm_num⟩
  | 16 => ⟨((-8815531809/576460752303423488), (-11438655/1125899906842624)), (519/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-1664214155505/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889274303646975/316912650057057350374175801344), (-492265877665/79228162514264337593543950336)), (5787/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944746898739127/19807040628566084398385987584), (-4429519929843/39614081257132168796771975168)), (407/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1889252883229753/2475880078570760549798248448), (-4705300821169/2475880078570760549798248448)), (6921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770918588414557/154742504910672534362390528), (-2352051931759/77371252455336267181195264)), (6923/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387324438664983/2417851639229258349412352), (-551103230761/1208925819614629174706176)), (1623/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629282197144639/302231454903657293676544), (-3856451360709/604462909807314587353088)), (5683/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887426493075425/75557863725914323419136), (-3132175217749/37778931862957161709568)), (9239/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648632171748547/2361183241434822606848), (-4696178256101/4722366482869645213696)), (6933/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405267075738951/147573952589676412928), (-6453858757131/590295810358705651712)), (4769/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822997552773103/73786976294838206464), (-8062245823275/73786976294838206464)), (23863/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822117022444815/9223372036854775808), (-9063047899065/9223372036854775808)), (6717/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796680782832927/576460752303423488), (-4527164602893/576460752303423488)), (26899/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597015028732951/72057594037927936), (-3956367941985/72057594037927936)), (11785/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490802477114283/36028797018963968), (-11849515392145/36028797018963968)), (35421/36028797018963968), by norm_num⟩
  | 3 => ⟨((372049643091911/2251799813685248), (-7388825152837/4503599627370496)), (44393/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112891879115987/2251799813685248), (-1840794516221/281474976710656)), (22285/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106371432348815/1125899906842624), (-5490387534265/281474976710656)), (67297/1125899906842624), by norm_num⟩
  | 0 => ⟨((271694870873959/281474976710656), (-43412675043163/1125899906842624)), (68185/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271694870873959/281474976710656), (-43412675043163/1125899906842624)), (260105135204124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1047344420428929/1125899906842624), (-20952130946031/281474976710656)), (273781/1125899906842624), by norm_num⟩
  | 2 => ⟨((1936062805798029/2251799813685248), (-311844380610493/2251799813685248)), (550117/1125899906842624), by norm_num⟩
  | 3 => ⟨((810705340698313/1125899906842624), (-134059498279515/562949953421312)), (2196665/2251799813685248), by norm_num⟩
  | 4 => ⟨((519899992497971/1125899906842624), (-772237393864395/2251799813685248)), (4209639/2251799813685248), by norm_num⟩
  | 5 => ⟨((107654644380137/1125899906842624), (-713182784431779/2251799813685248)), (3387523/1125899906842624), by norm_num⟩
  | 6 => ⟨((-410579653994079/4503599627370496), (-545536515773215/9007199254740992)), (11174309/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-1307841363/16777216)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-5382513031/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((21950095986785/2251799813685248), (1841273261737125/18014398509481984)), (18105631/9007199254740992), by norm_num⟩
  | 1 => ⟨((-883904445/34359738368), (-4634118745/17179869184)), (183/34359738368), by norm_num⟩
  | 2 => ⟨((291584313/8589934592), (24459410081/68719476736)), (485/68719476736), by norm_num⟩
  | 3 => ⟨((-1026010291/34359738368), (-21516595151/68719476736)), (429/68719476736), by norm_num⟩
  | 4 => ⟨((2707699979/137438953472), (28391764071/137438953472)), (71/17179869184), by norm_num⟩
  | 5 => ⟨((-1429155095/137438953472), (-29970997229/274877906944)), (301/137438953472), by norm_num⟩
  | 6 => ⟨((2514414819/549755813888), (26365059971/549755813888)), (133/137438953472), by norm_num⟩
  | 7 => ⟨((-1895909959/1099511627776), (-19879687075/1099511627776)), (403/1099511627776), by norm_num⟩
  | 8 => ⟨((2501707537/4398046511104), (26231816943/4398046511104)), (267/2199023255552), by norm_num⟩
  | 9 => ⟨((-733572179/4398046511104), (-15383837505/8796093022208)), (629/17592186044416), by norm_num⟩
  | 10 => ⟨((1548751229/35184372088832), (8119765825/17592186044416)), (167/17592186044416), by norm_num⟩
  | 11 => ⟨((-2972540569/281474976710656), (-31168767295/281474976710656)), (643/281474976710656), by norm_num⟩
  | 12 => ⟨((2614901659/1125899906842624), (13709360631/562949953421312)), (71/140737488355328), by norm_num⟩
  | 13 => ⟨((-1061673137/2251799813685248), (-1391530333/281474976710656)), (463/4503599627370496), by norm_num⟩
  | 14 => ⟨((1601037871/18014398509481984), (16787786627/18014398509481984)), (351/18014398509481984), by norm_num⟩
  | 15 => ⟨((-2253456389/144115188075855872), (-23628763385/144115188075855872)), (497/144115188075855872), by norm_num⟩
  | 16 => ⟨((743375075/288230376151711744), (31178830601/1152921504606846976)), (329/576460752303423488), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (1922283148671/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444613908902581/158456325028528675187087900672), (2274165387853/633825300114114700748351602688)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889389536537611/39614081257132168796771975168), (1278963223709/19807040628566084398385987584)), (1625/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472285634855201/618970019642690137449562112), (1358582800879/1237940039285380274899124224)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770808731839253/154742504910672534362390528), (42444620069/2417851639229258349412352)), (13817/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774597640734879/4835703278458516698824704), (2545923143091/9671406556917033397649408)), (3239/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258475247218517/604462909807314587353088), (2226928943521/604462909807314587353088)), (11339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235910324700173/9444732965739290427392), (3617346686045/75557863725914323419136)), (9215/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297157268539429/4722366482869645213696), (677943578355/1180591620717411303424)), (6913/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620922449185971/590295810358705651712), (1863341339523/295147905179352825856)), (9509/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911408647186421/36893488147419103232), (4655344616843/73786976294838206464)), (11891/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910958529167573/4611686018427387904), (5233128563681/9223372036854775808)), (1673/576460752303423488), by norm_num⟩
  | 6 => ⟨((1593165128386471/1152921504606846976), (5227965212463/1152921504606846976)), (13393/576460752303423488), by norm_num⟩
  | 5 => ⟨((149232766716135/18014398509481984), (4568666714935/144115188075855872)), (23457/144115188075855872), by norm_num⟩
  | 4 => ⟨((745279243649701/18014398509481984), (855176147235/4503599627370496)), (4403/4503599627370496), by norm_num⟩
  | 3 => ⟨((1487907353367395/9007199254740992), (8531510665495/9007199254740992)), (44097/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225242427971399/4503599627370496), (8501200883329/2251799813685248)), (44199/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212032950700655/2251799813685248), (25352517935421/2251799813685248)), (33277/562949953421312), by norm_num⟩
  | 0 => ⟨((2172543351007321/2251799813685248), (12525868947833/562949953421312)), (134135/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172543351007321/2251799813685248), (12525868947833/562949953421312)), (511684422019576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1047480825127011/1125899906842624), (48339986765817/1125899906842624)), (529595/2251799813685248), by norm_num⟩
  | 2 => ⟨((1944896376727891/2251799813685248), (89946200219669/1125899906842624)), (1030895/2251799813685248), by norm_num⟩
  | 3 => ⟨((1665450284559645/2251799813685248), (155374414585619/1125899906842624)), (1945497/2251799813685248), by norm_num⟩
  | 4 => ⟨((148612223388939/281474976710656), (459664951408647/2251799813685248)), (3414771/2251799813685248), by norm_num⟩
  | 5 => ⟨((266938933323221/1125899906842624), (970769497752253/4503599627370496)), (9999939/4503599627370496), by norm_num⟩
  | 6 => ⟨((21950095986785/2251799813685248), (1841273261737125/18014398509481984)), (18105631/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5382513031/67108864)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-11046456121/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((354322184742449/4503599627370496), (-126772039255821/2251799813685248)), (11218563/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7320573911/34359738368), (5238419287/34359738368)), (117/34359738368), by norm_num⟩
  | 2 => ⟨((4956120413/17179869184), (-14185902403/68719476736)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((-4473807627/17179869184), (6402689309/34359738368)), (291/68719476736), by norm_num⟩
  | 4 => ⟨((3028823911/17179869184), (-8669402035/68719476736)), (199/68719476736), by norm_num⟩
  | 5 => ⟨((-6561765761/68719476736), (4695435185/68719476736)), (109/68719476736), by norm_num⟩
  | 6 => ⟨((11846394059/274877906944), (-4238491399/137438953472)), (99/137438953472), by norm_num⟩
  | 7 => ⟨((-18331788465/1099511627776), (13117768555/1099511627776)), (309/1099511627776), by norm_num⟩
  | 8 => ⟨((3102712715/549755813888), (-8880893943/2199023255552)), (211/2199023255552), by norm_num⟩
  | 9 => ⟨((-14937425407/8796093022208), (5344423695/4398046511104)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((16180519151/35184372088832), (-11578374129/35184372088832)), (35/4398046511104), by norm_num⟩
  | 11 => ⟨((-15933693869/140737488355328), (11401752141/140737488355328)), (139/70368744177664), by norm_num⟩
  | 12 => ⟨((7191540481/281474976710656), (-10292172393/562949953421312)), (253/562949953421312), by norm_num⟩
  | 13 => ⟨((-5992323891/1125899906842624), (4287956849/1125899906842624)), (53/562949953421312), by norm_num⟩
  | 14 => ⟨((1159108137/1125899906842624), (-6635429947/9007199254740992)), (165/9007199254740992), by norm_num⟩
  | 15 => ⟨((-13392738233/72057594037927936), (2395876987/18014398509481984)), (15/4503599627370496), by norm_num⟩
  | 16 => ⟨((4533525933/144115188075855872), (-12976310313/576460752303423488)), (327/576460752303423488), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-809055543613/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889183108380149/316912650057057350374175801344), (-478531313383/316912650057057350374175801344)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236161136040751/4951760157141521099596496896), (-1076477108413/39614081257132168796771975168)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889036006317651/2475880078570760549798248448), (-571742252199/1237940039285380274899124224)), (13793/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885351207904879/77371252455336267181195264), (-1143178158079/154742504910672534362390528)), (6897/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549095840683373/9671406556917033397649408), (-1071404143713/9671406556917033397649408)), (12933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258388466853421/604462909807314587353088), (-468576686983/302231454903657293676544)), (11317/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471785502751587/18889465931478580854784), (-1522264656845/75557863725914323419136)), (2299/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297052205797007/4722366482869645213696), (-1141165384871/4722366482869645213696)), (3449/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620778600202353/590295810358705651712), (-98014788257/36893488147419103232)), (4743/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113914900025273/4611686018427387904), (-489749491369/18446744073709551616)), (23719/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821717061955665/9223372036854775808), (-2202089679273/9223372036854775808)), (13345/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592966703330965/1152921504606846976), (-2199863051469/1152921504606846976)), (26697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596845137819493/72057594037927936), (-961189091727/72057594037927936)), (2921/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490304218083179/36028797018963968), (-2878570716905/36028797018963968)), (8767/9007199254740992), by norm_num⟩
  | 3 => ⟨((371898912829683/2251799813685248), (-3589486076923/9007199254740992)), (43863/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224637339975445/4503599627370496), (-7152856698933/4503599627370496)), (87813/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105585402203461/1125899906842624), (-5332114296975/1125899906842624)), (131937/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085499591115247/1125899906842624), (-21069619864621/2251799813685248)), (16547/140737488355328), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085499591115247/1125899906842624), (-21069619864621/2251799813685248)), (63121796191167787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((261612593830631/281474976710656), (-40627170513119/2251799813685248)), (128865/562949953421312), by norm_num⟩
  | 2 => ⟨((1944481458101201/2251799813685248), (-75520599252857/2251799813685248)), (488387/1125899906842624), by norm_num⟩
  | 3 => ⟨((838286058343987/1125899906842624), (-65213792122819/1125899906842624)), (1752453/2251799813685248), by norm_num⟩
  | 4 => ⟨((9693227844427/17592186044416), (-194219086140997/2251799813685248)), (703145/562949953421312), by norm_num⟩
  | 5 => ⟨((83360969851567/281474976710656), (-107013980465415/1125899906842624)), (448077/281474976710656), by norm_num⟩
  | 6 => ⟨((354322184742449/4503599627370496), (-126772039255821/2251799813685248)), (11218563/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-11046456121/134217728)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile055Terms1
